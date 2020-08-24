// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "tools/transform.h"
#include "ir/globals.h"
#include "ir/state.h"
#include "smt/expr.h"
#include "smt/smt.h"
#include "smt/solver.h"
#include "util/config.h"
#include "util/errors.h"
#include "util/stopwatch.h"
#include "util/symexec.h"
#include <algorithm>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <stack>
#include <list>

using namespace IR;
using namespace smt;
using namespace tools;
using namespace util;
using namespace std;


static bool is_undef(const expr &e) {
  if (e.isConst())
    return false;
  return check_expr(expr::mkForAll(e.vars(), expr::mkVar("#undef", e) != e)).
           isUnsat();
}

static void print_single_varval(ostream &os, State &st, const Model &m,
                                const Value *var, const Type &type,
                                const StateValue &val) {
  if (!val.isValid()) {
    os << "(invalid expr)";
    return;
  }

  // if the model is partial, we don't know for sure if it's poison or not
  // this happens if the poison constraint depends on an undef
  // however, cexs are usually triggered by the worst case, which is poison
  if (auto v = m.eval(val.non_poison);
      (!v.isConst() || v.isFalse())) {
    os << "poison";
    return;
  }

  if (auto *in = dynamic_cast<const Input*>(var)) {
    uint64_t n;
    ENSURE(m[in->getTyVar()].isUInt(n));
    if (n == 1) {
      os << "undef";
      return;
    }
    assert(n == 0);
  }

  expr partial = m.eval(val.value);
  if (is_undef(partial)) {
    os << "undef";
    return;
  }

  type.printVal(os, st, m.eval(val.value, true));

  // undef variables may not have a model since each read uses a copy
  // TODO: add intervals of possible values for ints at least?
  if (!partial.isConst()) {
    // some functions / vars may not have an interpretation because it's not
    // needed, not because it's undef
    bool found_undef = false;
    for (auto &var : partial.vars()) {
      if ((found_undef = isUndef(var)))
        break;
    }
    if (found_undef)
      os << "\t[based on undef value]";
  }
}

static void print_varval(ostream &os, State &st, const Model &m,
                         const Value *var, const Type &type,
                         const StateValue &val) {
  if (!type.isAggregateType()) {
    print_single_varval(os, st, m, var, type, val);
    return;
  }

  os << (type.isStructType() ? "{ " : "< ");
  auto agg = type.getAsAggregateType();
  for (unsigned i = 0, e = agg->numElementsConst(); i < e; ++i) {
    if (i != 0)
      os << ", ";
    print_varval(os, st, m, var, agg->getChild(i), agg->extract(val, i));
  }
  os << (type.isStructType() ? " }" : " >");
}


using print_var_val_ty = function<void(ostream&, const Model&)>;

static void error(Errors &errs, State &src_state, State &tgt_state,
                  const Result &r, const Value *var,
                  const char *msg, bool check_each_var,
                  print_var_val_ty print_var_val) {

  if (r.isInvalid()) {
    errs.add("Invalid expr", false);
    return;
  }

  if (r.isTimeout()) {
    errs.add("Timeout", false);
    return;
  }

  if (r.isError()) {
    errs.add("SMT Error: " + r.getReason(), false);
    return;
  }

  if (r.isSkip()) {
    errs.add("Skip", false);
    return;
  }

  stringstream s;
  string empty;
  auto &var_name = var ? var->getName() : empty;
  auto &m = r.getModel();

  s << msg;
  if (!var_name.empty())
    s << " for " << *var;
  s << "\n\nExample:\n";

  for (auto &[var, val, used] : src_state.getValues()) {
    (void)used;
    if (!dynamic_cast<const Input*>(var) &&
        !dynamic_cast<const ConstantInput*>(var))
      continue;
    s << *var << " = ";
    print_varval(s, src_state, m, var, var->getType(), val.first);
    s << '\n';
  }

  set<string> seen_vars;
  for (auto st : { &src_state, &tgt_state }) {
    if (!check_each_var) {
      if (st->isSource()) {
        s << "\nSource:\n";
      } else {
        s << "\nTarget:\n";
      }
    }

    for (auto &[var, val, used] : st->getValues()) {
      (void)used;
      auto &name = var->getName();
      if (name == var_name)
        break;

      if (name[0] != '%' ||
          dynamic_cast<const Input*>(var) ||
          (check_each_var && !seen_vars.insert(name).second))
        continue;

      s << *var << " = ";
      print_varval(s, const_cast<State&>(*st), m, var, var->getType(),
                   val.first);
      s << '\n';
    }

    st->getMemory().print(s, m);
  }

  print_var_val(s, m);
  errs.add(s.str(), true);
}


static expr preprocess(Transform &t, const set<expr> &qvars0,
                       const set<expr> &undef_qvars, expr && e) {
  if (hit_half_memory_limit())
    return expr::mkForAll(qvars0, move(e));

  // TODO: benchmark
  if (0) {
    expr var = expr::mkBoolVar("malloc_never_fails");
    e = expr::mkIf(var,
                   e.subst(var, true).simplify(),
                   e.subst(var, false).simplify());
  }

  // eliminate all quantified boolean vars; Z3 gets too slow with those
  auto qvars = qvars0;
  for (auto &var : qvars0) {
    if (!var.isBool())
      continue;
    if (hit_half_memory_limit())
      break;

    e = e.subst(var, true).simplify() &&
        e.subst(var, false).simplify();
    qvars.erase(var);
  }

  // TODO: maybe try to instantiate undet_xx vars?
  if (undef_qvars.empty() || hit_half_memory_limit())
    return expr::mkForAll(qvars, move(e));

  // manually instantiate all ty_%v vars
  map<expr, expr> instances({ { move(e), true } });
  map<expr, expr> instances2;

  expr nums[3] = { expr::mkUInt(0, 2), expr::mkUInt(1, 2), expr::mkUInt(2, 2) };

  for (auto &i : t.src.getInputs()) {
    auto in = dynamic_cast<const Input*>(&i);
    if (!in)
      continue;
    auto var = in->getTyVar();

    for (auto &[e, v] : instances) {
      for (unsigned i = 0; i <= 2; ++i) {
        if (config::disable_undef_input && i == 1)
          continue;
        if (config::disable_poison_input && i == 2)
          continue;

        expr newexpr = e.subst(var, nums[i]);
        if (newexpr.eq(e)) {
          instances2[move(newexpr)] = v;
          break;
        }

        newexpr = newexpr.simplify();
        if (newexpr.isFalse())
          continue;

        // keep 'var' variables for counterexample printing
        instances2.try_emplace(move(newexpr), v && var == nums[i]);
      }
    }
    instances = move(instances2);

    // Bail out if it gets too big. It's very likely we can't solve it anyway.
    if (instances.size() >= 128 || hit_half_memory_limit())
      break;
  }

  expr insts(false);
  for (auto &[e, v] : instances) {
    insts |= expr::mkForAll(qvars, move(const_cast<expr&>(e))) && v;
  }

  // TODO: try out instantiating the undefs in forall quantifier

  return insts;
}


static void
check_refinement(Errors &errs, Transform &t, State &src_state, State &tgt_state,
                 const Value *var, const Type &type,
                 const expr &dom_a, const expr &fndom_a, const State::ValTy &ap,
                 const expr &dom_b, const expr &fndom_b, const State::ValTy &bp,
                 bool check_each_var) {
  auto &a = ap.first;
  auto &b = bp.first;

  auto &uvars = ap.second;
  auto qvars = src_state.getQuantVars();
  qvars.insert(ap.second.begin(), ap.second.end());

  auto err = [&](const Result &r, print_var_val_ty print, const char *msg) {
    error(errs, src_state, tgt_state, r, var, msg, check_each_var, print);
  };

  auto print_value = [&](ostream &s, const Model &m) {
    s << "Source value: ";
    print_varval(s, src_state, m, var, type, a);
    s << "\nTarget value: ";
    print_varval(s, tgt_state, m, var, type, b);
  };

  AndExpr axioms = src_state.getAxioms();
  axioms.add(tgt_state.getAxioms());

  // restrict type variable from taking disabled values
  if (config::disable_undef_input || config::disable_poison_input) {
    for (auto &i : t.src.getInputs()) {
      if (auto in = dynamic_cast<const Input*>(&i)) {
        auto var = in->getTyVar();
        if (config::disable_undef_input) {
          if (config::disable_poison_input)
            axioms.add(var == 0);
          else
            axioms.add(var != 1);
        } else if (config::disable_poison_input)
          axioms.add(var.extract(1, 1) == 0);
      }
    }
  }

  // note that precondition->toSMT() may add stuff to getPre,
  // so order here matters
  // FIXME: broken handling of transformation precondition
  //src_state.startParsingPre();
  //expr pre = t.precondition ? t.precondition->toSMT(src_state) : true;
  auto pre_src_and = src_state.getPre();
  auto &pre_tgt_and = tgt_state.getPre();

  // optimization: rewrite "tgt /\ (src -> foo)" to "tgt /\ foo" if src = tgt
  pre_src_and.del(pre_tgt_and);
  expr pre_src = pre_src_and();
  expr pre_tgt = pre_tgt_and();

  expr axioms_expr = axioms();
  expr dom = dom_a && dom_b;

  pre_tgt &= src_state.getOOM()();
  pre_tgt &= !tgt_state.sinkDomain();
  pre_tgt &= src_state.getPre(true)();
  pre_tgt &= tgt_state.getPre(true)();

  auto [poison_cnstr, value_cnstr] = type.refines(src_state, tgt_state, a, b);

  auto src_mem = src_state.returnMemory();
  auto tgt_mem = tgt_state.returnMemory();
  auto [memory_cnstr0, ptr_refinement0] = src_mem.refined(tgt_mem, false);
  auto &ptr_refinement = ptr_refinement0;
  auto memory_cnstr = memory_cnstr0.isTrue() ? memory_cnstr0
                                             : value_cnstr && memory_cnstr0;

  if (!memory_cnstr.isConst()) {
    auto &undef = src_mem.getUndefVars();
    qvars.insert(undef.begin(), undef.end());
  }

  if (check_expr(axioms_expr && (pre_src && pre_tgt)).isUnsat()) {
    errs.add("Precondition is always false", false);
    return;
  }

  auto mk_fml = [&](expr &&refines) -> expr {
    // from the check above we already know that
    // \exists v,v' . pre_tgt(v') && pre_src(v) is SAT (or timeout)
    // so \forall v . pre_tgt && (!pre_src(v) || refines) simplifies to:
    // (pre_tgt && !pre_src) || (!pre_src && false) ->   [assume refines=false]
    // \forall v . (pre_tgt && !pre_src(v)) ->  [\exists v . pre_src(v)]
    // false
    if (refines.isFalse())
      return move(refines);

    auto fml = pre_tgt && pre_src.implies(refines);
    return axioms_expr && preprocess(t, qvars, uvars, move(fml));
  };

  auto print_ptr_load = [&](ostream &s, const Model &m) {
    Pointer p(src_mem, m[ptr_refinement()]);
    s << "\nMismatch in " << p
      << "\nSource value: " << Byte(src_mem, m[src_mem.load(p)()])
      << "\nTarget value: " << Byte(tgt_mem, m[tgt_mem.load(p)()]);
  };

  expr dom_constr;
  if (dom_a.eq(fndom_a)) {
    if (dom_b.eq(fndom_b)) // A /\ B /\ A != B
       dom_constr = false;
    else // A /\ B /\ A != C
      dom_constr = fndom_a && fndom_b && !dom_b;
  } else if (dom_b.eq(fndom_b)) { // A /\ B /\ C != B
    dom_constr = fndom_a && fndom_b && !dom_a;
  } else {
    dom_constr = (fndom_a && fndom_b) && dom_a != dom_b;
  }

  Solver::check({
    { mk_fml(fndom_a.notImplies(fndom_b)),
      [&](const Result &r) {
        err(r, [](ostream&, const Model&){},
            "Source is more defined than target");
      }},
    { mk_fml(move(dom_constr)),
      [&](const Result &r) {
        err(r, [](ostream&, const Model&){},
            "Source and target don't have the same return domain");
      }},
    { mk_fml(dom && !poison_cnstr),
      [&](const Result &r) {
        err(r, print_value, "Target is more poisonous than source");
      }},
    { mk_fml(dom && !value_cnstr),
      [&](const Result &r) {
        err(r, print_value, "Value mismatch");
      }},
    { mk_fml(dom && !memory_cnstr),
      [&](const Result &r) {
        err(r, print_ptr_load, "Mismatch in memory");
      }}
  });
}

static bool has_nullptr(const Value *v) {
  if (dynamic_cast<const NullPointerValue*>(v) ||
      (dynamic_cast<const UndefValue*>(v) && hasPtr(v->getType())))
      // undef pointer points to the nullblk
    return true;

  if (auto agg = dynamic_cast<const AggregateValue*>(v)) {
    for (auto val : agg->getVals()) {
      if (has_nullptr(val))
        return true;
    }
  }

  return false;
}

static unsigned num_ptrs(const Type &ty) {
  unsigned n = ty.isPtrType();
  if (auto aty = ty.getAsAggregateType())
    n += aty->numPointerElements();
  return n;
}

static bool returns_local(const Value &v) {
  return dynamic_cast<const Alloc*>(&v) ||
         dynamic_cast<const Malloc*>(&v) ||
         dynamic_cast<const Calloc*>(&v);
}

static bool may_be_nonlocal(Value *ptr) {
  vector<Value*> todo = { ptr };
  set<Value*> seen;
  do {
    ptr = todo.back();
    todo.pop_back();
    if (!seen.insert(ptr).second)
      continue;

    if (returns_local(*ptr))
      continue;

    if (auto gep = dynamic_cast<GEP*>(ptr)) {
      todo.emplace_back(&gep->getPtr());
      continue;
    }

    if (auto c = isNoOp(*ptr)) {
      todo.emplace_back(c);
      continue;
    }

    if (auto phi = dynamic_cast<Phi*>(ptr)) {
      for (auto &op : phi->operands())
        todo.emplace_back(op);
      continue;
    }

    if (auto s = dynamic_cast<Select*>(ptr)) {
      todo.emplace_back(s->getTrueValue());
      todo.emplace_back(s->getFalseValue());
      continue;
    }
    return true;

  } while (!todo.empty());

  return false;
}

static pair<Value*, uint64_t> collect_gep_offsets(Value &v) {
  Value *ptr = &v;
  uint64_t offset = 0;

  while (true) {
    if (auto gep = dynamic_cast<GEP*>(ptr)) {
      uint64_t off = gep->getMaxGEPOffset();
      if (off != UINT64_MAX) {
        ptr = &gep->getPtr();
        offset += off;
        continue;
      }
    }
    break;
  }

  return { ptr, offset };
}

static unsigned returns_nonlocal(const Instr &inst,
                                 set<pair<Value*, uint64_t>> &cache) {
  bool rets_nonloc = false;

  if (dynamic_cast<const FnCall*>(&inst) ||
      isCast(ConversionOp::Int2Ptr, inst)) {
    rets_nonloc = true;
  }
  else if (auto load = dynamic_cast<const Load *>(&inst)) {
    if (may_be_nonlocal(&load->getPtr())) {
      auto [ptr, offset] = collect_gep_offsets(load->getPtr());
      rets_nonloc = cache.emplace(ptr, offset).second;
    }
  }
  return rets_nonloc ? num_ptrs(inst.getType()) : 0;
}


static void calculateAndInitConstants(Transform &t) {
  const auto &globals_tgt = t.tgt.getGlobalVars();
  const auto &globals_src = t.src.getGlobalVars();
  unsigned num_globals_src = globals_src.size();
  unsigned num_globals = num_globals_src;

  // FIXME: varies among address spaces
  bits_program_pointer = t.src.bitsPointers();
  assert(bits_program_pointer > 0 && bits_program_pointer <= 64);
  assert(bits_program_pointer == t.tgt.bitsPointers());
  heap_block_alignment = 8;

  num_consts_src = 0;
  num_extra_nonconst_tgt = 0;

  for (auto GV : globals_src) {
    if (GV->isConst())
      ++num_consts_src;
  }

  for (auto GVT : globals_tgt) {
    auto I = find_if(globals_src.begin(), globals_src.end(),
      [GVT](auto *GV) -> bool { return GVT->getName() == GV->getName(); });
    if (I == globals_src.end()) {
      ++num_globals;
      if (!GVT->isConst())
        ++num_extra_nonconst_tgt;
    }
  }

  unsigned num_ptrinputs = 0;
  for (auto &arg : t.src.getInputs()) {
    num_ptrinputs += num_ptrs(arg.getType());
  }

  // The number of instructions that can return a pointer to a non-local block.
  unsigned num_nonlocals_inst_src = 0, num_nonlocals_inst_tgt = 0;
  // The number of local blocks.
  num_locals_src = 0;
  num_locals_tgt = 0;
  uint64_t max_gep_src = 0, max_gep_tgt = 0;
  uint64_t max_alloc_size = 0;
  uint64_t max_access_size = 0;

  bool nullptr_is_used = false;
  has_int2ptr      = false;
  has_ptr2int      = false;
  has_alloca       = false;
  has_dead_allocas = false;
  has_malloc       = false;
  has_free         = false;
  has_fncall       = false;
  has_null_block   = false;
  does_ptr_store   = false;
  does_ptr_mem_access = false;
  does_int_mem_access = false;

  // Mininum access size (in bytes)
  uint64_t min_access_size = 8;
  bool does_mem_access = false;
  bool has_ptr_load = false;
  does_sub_byte_access = false;
  bool has_vector_bitcast = false;

  for (auto fn : { &t.src, &t.tgt }) {
    unsigned &cur_num_locals = fn == &t.src ? num_locals_src : num_locals_tgt;
    uint64_t &cur_max_gep    = fn == &t.src ? max_gep_src : max_gep_tgt;
    auto &num_nonlocals_inst = fn == &t.src ? num_nonlocals_inst_src
                                            : num_nonlocals_inst_tgt;

    for (auto &v : fn->getInputs()) {
      auto *i = dynamic_cast<const Input *>(&v);
      if (i && i->hasAttribute(ParamAttrs::Dereferenceable)) {
        does_mem_access = true;
        uint64_t deref_bytes = i->getAttributes().getDerefBytes();
        min_access_size = gcd(min_access_size, deref_bytes);
        max_access_size = max(max_access_size, deref_bytes);
      }
    }

    set<pair<Value*, uint64_t>> nonlocal_cache;
    for (auto BB : fn->getBBs()) {
      for (auto &i : BB->instrs()) {
        if (returns_local(i))
          ++cur_num_locals;
        else
          num_nonlocals_inst += returns_nonlocal(i, nonlocal_cache);

        for (auto op : i.operands()) {
          nullptr_is_used |= has_nullptr(op);
        }

        if (auto *fc = dynamic_cast<const FnCall*>(&i)) {
          has_fncall |= true;
          has_free   |= !fc->getAttributes().has(FnAttrs::NoFree);
        }

        if (auto *mi = dynamic_cast<const MemInstr *>(&i)) {
          max_alloc_size  = max(max_alloc_size, mi->getMaxAllocSize());
          max_access_size = max(max_access_size, mi->getMaxAccessSize());
          cur_max_gep     = add_saturate(cur_max_gep, mi->getMaxGEPOffset());

          auto info = mi->getByteAccessInfo();
          has_ptr_load         |= info.doesPtrLoad;
          does_ptr_store       |= info.doesPtrStore;
          does_int_mem_access  |= info.hasIntByteAccess;
          does_ptr_mem_access  |= info.hasPtrByteAccess;
          does_sub_byte_access |= info.hasSubByteAccess;
          does_mem_access      |= info.doesMemAccess();
          min_access_size       = gcd(min_access_size, info.byteSize);

          if (auto alloc = dynamic_cast<const Alloc*>(&i)) {
            has_alloca = true;
            has_dead_allocas |= alloc->initDead();
          }
          else if (auto alloc = dynamic_cast<const Malloc*>(&i)) {
            has_malloc  = true;
            has_free   |= alloc->isRealloc();
          } else {
            has_malloc |= dynamic_cast<const Calloc*>(&i) != nullptr;
            has_free   |= dynamic_cast<const Free*>(&i) != nullptr;
          }

        } else if (isCast(ConversionOp::Int2Ptr, i) ||
                   isCast(ConversionOp::Ptr2Int, i)) {
          max_alloc_size = max_access_size = cur_max_gep = UINT64_MAX;
          has_int2ptr |= isCast(ConversionOp::Int2Ptr, i) != nullptr;
          has_ptr2int |= isCast(ConversionOp::Ptr2Int, i) != nullptr;

        } else if (auto *bc = isCast(ConversionOp::BitCast, i)) {
          auto &t = bc->getType();
          has_vector_bitcast |= t.isVectorType();
          does_sub_byte_access |= hasSubByte(t);
          min_access_size = gcd(min_access_size, getCommonAccessSize(t));
        }
      }
    }
  }
  unsigned num_locals = max(num_locals_src, num_locals_tgt);

  uint64_t min_global_size = UINT64_MAX;
  for (auto glbs : { &globals_src, &globals_tgt }) {
    for (auto &glb : *glbs) {
      auto sz = max(glb->size(), (uint64_t)1u);
      max_access_size = max(sz, max_access_size);
      min_global_size = min_global_size != UINT64_MAX
                          ? gcd(sz, min_global_size)
                          : sz;
      min_global_size = gcd(min_global_size, glb->getAlignment());
    }
  }

  // check if null block is needed
  // Global variables cannot be null pointers
  has_null_block = num_ptrinputs > 0 || nullptr_is_used || has_malloc ||
                  has_ptr_load || has_fncall;

  // + 1 is sufficient to give 1 degree of freedom for the target to trigger UB
  // in case a different pointer from source is produced.
  auto num_max_nonlocals_inst
    = max(num_nonlocals_inst_src, num_nonlocals_inst_tgt);
  if (num_nonlocals_inst_src && num_nonlocals_inst_tgt)
    ++num_max_nonlocals_inst;

  num_nonlocals_src = num_globals_src + num_ptrinputs + num_max_nonlocals_inst +
                      has_null_block;

  // Allow at least one non-const global for calls to change
  num_nonlocals_src += has_fncall;

  num_nonlocals = num_nonlocals_src + num_globals - num_globals_src;

  if (!does_int_mem_access && !does_ptr_mem_access && has_fncall)
    does_int_mem_access = true;

  auto has_attr = [&](ParamAttrs::Attribute a) -> bool {
    for (auto fn : { &t.src, &t.tgt }) {
      for (auto &v : fn->getInputs()) {
        auto i = dynamic_cast<const Input*>(&v);
        if (i && i->hasAttribute(a))
          return true;
      }
    }
    return false;
  };
  // The number of bits needed to encode pointer attributes
  // nonnull and byval isn't encoded in ptr attribute bits
  bool has_byval = has_attr(ParamAttrs::ByVal);
  has_nocapture = has_attr(ParamAttrs::NoCapture);
  has_readonly = has_attr(ParamAttrs::ReadOnly);
  has_readnone = has_attr(ParamAttrs::ReadNone);
  bits_for_ptrattrs = has_nocapture + has_readonly + has_readnone;

  // ceil(log2(maxblks)) + 1 for local bit
  bits_for_bid = max(1u, ilog2_ceil(max(num_locals, num_nonlocals), false))
                   + (num_locals && num_nonlocals);

  // reserve a multiple of 4 for the number of offset bits to make SMT &
  // counterexamples more readable
  // Allow an extra bit for the sign
  auto max_geps
    = ilog2_ceil(add_saturate(max(max_gep_src, max_gep_tgt), max_access_size),
                 true) + 1;
  bits_for_offset = min(round_up(max_geps, 4), (uint64_t)t.src.bitsPtrOffset());

  // we need an extra bit because 1st bit of size is always 0
  bits_size_t = ilog2_ceil(max_alloc_size, true);
  bits_size_t = min(max(bits_for_offset, bits_size_t)+1, bits_program_pointer);

  // size of byte
  if (num_globals != 0) {
    if (does_mem_access || has_vector_bitcast)
      min_access_size = gcd(min_global_size, min_access_size);
    else {
      min_access_size = min_global_size;
      while (min_access_size > 8) {
        if (min_access_size % 2) {
          min_access_size = 1;
          break;
        }
        min_access_size /= 2;
      }
    }
  }
  if (has_byval)
    min_access_size = 1;
  bits_byte = 8 * ((does_mem_access || num_globals != 0)
                     ? (unsigned)min_access_size : 1);

  strlen_unroll_cnt = 10;
  memcmp_unroll_cnt = 10;

  little_endian = t.src.isLittleEndian();

  if (config::debug)
    config::dbg() << "num_max_nonlocals_inst: " << num_max_nonlocals_inst
                  << "\nnum_locals_src: " << num_locals_src
                  << "\nnum_locals_tgt: " << num_locals_tgt
                  << "\nnum_nonlocals_src: " << num_nonlocals_src
                  << "\nnum_nonlocals: " << num_nonlocals
                  << "\nbits_for_bid: " << bits_for_bid
                  << "\nbits_for_offset: " << bits_for_offset
                  << "\nbits_size_t: " << bits_size_t
                  << "\nbits_program_pointer: " << bits_program_pointer
                  << "\nmax_alloc_size: " << max_alloc_size
                  << "\nmin_access_size: " << min_access_size
                  << "\nmax_access_size: " << max_access_size
                  << "\nbits_byte: " << bits_byte
                  << "\nstrlen_unroll_cnt: " << strlen_unroll_cnt
                  << "\nmemcmp_unroll_cnt: " << memcmp_unroll_cnt
                  << "\nlittle_endian: " << little_endian
                  << "\nnullptr_is_used: " << nullptr_is_used
                  << "\nhas_int2ptr: " << has_int2ptr
                  << "\nhas_ptr2int: " << has_ptr2int
                  << "\nhas_malloc: " << has_malloc
                  << "\nhas_free: " << has_free
                  << "\nhas_null_block: " << has_null_block
                  << "\ndoes_ptr_store: " << does_ptr_store
                  << "\ndoes_mem_access: " << does_mem_access
                  << "\ndoes_ptr_mem_access: " << does_ptr_mem_access
                  << "\ndoes_int_mem_access: " << does_int_mem_access
                  << "\ndoes_sub_byte_access: " << does_sub_byte_access
                  << '\n';
}


namespace tools {

TransformVerify::TransformVerify(Transform &t, bool check_each_var) :
  t(t), check_each_var(check_each_var) {
  if (check_each_var) {
    for (auto &i : t.tgt.instrs()) {
      tgt_instrs.emplace(i.getName(), &i);
    }
  }
}

Errors TransformVerify::verify() const {
  try {
    t.tgt.syncDataWithSrc(t.src);
  } catch (AliveException &ae) {
    return Errors(move(ae));
  }

  // Check sizes of global variables
  auto globals_tgt = t.tgt.getGlobalVars();
  auto globals_src = t.src.getGlobalVars();
  for (auto GVS : globals_src) {
    auto I = find_if(globals_tgt.begin(), globals_tgt.end(),
      [GVS](auto *GV) -> bool { return GVS->getName() == GV->getName(); });
    if (I == globals_tgt.end())
      continue;

    auto GVT = *I;
    if (GVS->size() != GVT->size()) {
      stringstream ss;
      ss << "Unsupported interprocedural transformation: global variable "
        << GVS->getName() << " has different size in source and target ("
        << GVS->size() << " vs " << GVT->size()
        << " bytes)";
      return { ss.str(), false };
    } else if (GVS->isConst() && !GVT->isConst()) {
      stringstream ss;
      ss << "Transformation is incorrect because global variable "
        << GVS->getName() << " is const in source but not in target";
      return { ss.str(), true };
    } else if (!GVS->isConst() && GVT->isConst()) {
      stringstream ss;
      ss << "Unsupported interprocedural transformation: global variable "
        << GVS->getName() << " is const in target but not in source";
      return { ss.str(), false };
    }
  }

  StopWatch symexec_watch;
  calculateAndInitConstants(t);
  State::resetGlobals();
  State src_state(t.src, true), tgt_state(t.tgt, false);

  try {
    sym_exec(src_state);
    tgt_state.syncSEdataWithSrc(src_state);
    sym_exec(tgt_state);
    src_state.mkAxioms(tgt_state);
  } catch (AliveException e) {
    return move(e);
  }

  symexec_watch.stop();
  if (symexec_watch.seconds() > 5) {
    cerr << "WARNING: slow vcgen! Took " << symexec_watch << '\n';
  }

  Errors errs;

  if (check_each_var) {
    for (auto &[var, val, used] : src_state.getValues()) {
      (void)used;
      auto &name = var->getName();
      if (name[0] != '%' || !dynamic_cast<const Instr*>(var))
        continue;

      // TODO: add data-flow domain tracking for Alive, but not for TV
      check_refinement(errs, t, src_state, tgt_state, var, var->getType(),
                       true, true, val,
                       true, true, tgt_state.at(*tgt_instrs.at(name)),
                       check_each_var);
      if (errs)
        return errs;
    }
  }

  check_refinement(errs, t, src_state, tgt_state, nullptr, t.src.getType(),
                   src_state.returnDomain()(), src_state.functionDomain()(),
                   src_state.returnVal(),
                   tgt_state.returnDomain()(), tgt_state.functionDomain()(),
                   tgt_state.returnVal(),
                   check_each_var);

  return errs;
}


TypingAssignments::TypingAssignments(const expr &e) : s(true), sneg(true) {
  if (e.isTrue()) {
    has_only_one_solution = true;
  } else {
    EnableSMTQueriesTMP tmp;
    s.add(e);
    sneg.add(!e);
    r = s.check();
  }
}

TypingAssignments::operator bool() const {
  return !is_unsat && (has_only_one_solution || r.isSat());
}

void TypingAssignments::operator++(void) {
  if (has_only_one_solution) {
    is_unsat = true;
  } else {
    EnableSMTQueriesTMP tmp;
    s.block(r.getModel(), &sneg);
    r = s.check();
    assert(r.isSat() || r.isUnsat());
  }
}

TypingAssignments TransformVerify::getTypings() const {
  auto c = t.src.getTypeConstraints() && t.tgt.getTypeConstraints();

  if (t.precondition)
    c &= t.precondition->getTypeConstraints();

  // return type
  c &= t.src.getType() == t.tgt.getType();

  if (check_each_var) {
    for (auto &i : t.src.instrs()) {
      if (!i.isVoid())
        c &= i.eqType(*tgt_instrs.at(i.getName()));
    }
  }
  return { move(c) };
}

void TransformVerify::fixupTypes(const TypingAssignments &ty) {
  if (ty.has_only_one_solution)
    return;
  if (t.precondition)
    t.precondition->fixupTypes(ty.r.getModel());
  t.src.fixupTypes(ty.r.getModel());
  t.tgt.fixupTypes(ty.r.getModel());
}

static map<string_view, Instr*> can_remove_init(Function &fn) {
  map<string_view, Instr*> to_remove;
  auto &bb = fn.getFirstBB();
  if (bb.getName() != "#init")
    return to_remove;

  bool has_int2ptr = false;
  for (auto &i : fn.instrs()) {
    if (isCast(ConversionOp::Int2Ptr, i)) {
      has_int2ptr = true;
      break;
    }
  }

  vector<Value*> worklist;
  set<const Value*> seen;
  auto users = fn.getUsers();

  for (auto &i : bb.instrs()) {
    if (!dynamic_cast<const Store*>(&i))
      continue;
    auto gvar = i.operands()[1];
    worklist.emplace_back(gvar);
    seen.emplace(&i);

    bool needed = false;
    do {
      auto user = worklist.back();
      worklist.pop_back();
      if (!seen.emplace(user).second)
        continue;

      // OK, we can't observe which memory it reads
      if (dynamic_cast<FnCall*>(user))
        continue;

      if (isCast(ConversionOp::Ptr2Int, *user)) {
        // int2ptr can potentially alias with anything, so play on the safe side
        if (has_int2ptr) {
          needed = true;
          break;
        }
        continue;
      }

      // no useful users
      if (dynamic_cast<ICmp*>(user) ||
          dynamic_cast<Return*>(user))
        continue;

      if (dynamic_cast<MemInstr*>(user) && !dynamic_cast<GEP*>(user)) {
        needed = true;
        break;
      }

      for (auto p = users.equal_range(user); p.first != p.second; ++p.first) {
        worklist.emplace_back(p.first->second);
      }
    } while (!worklist.empty());

    worklist.clear();
    seen.clear();

    if (!needed)
      to_remove.emplace(gvar->getName(), const_cast<Instr*>(&i));
  }
  return to_remove;
}

void Transform::preprocess(unsigned unroll_factor) {
  // remove store of initializers to global variables that aren't needed to
  // verify the transformation
  // We only remove inits if it's possible to remove from both programs to keep
  // memories syntactically equal
  auto remove_init_tgt = can_remove_init(tgt);
  for (auto &[name, isrc] : can_remove_init(src)) {
    auto Itgt = remove_init_tgt.find(name);
    if (Itgt == remove_init_tgt.end())
      continue;
    src.getFirstBB().delInstr(isrc);
    tgt.getFirstBB().delInstr(Itgt->second);
    // TODO: check that tgt init refines that of src
  }

  // remove side-effect free instructions without users
  vector<Instr*> to_remove;
  for (auto fn : { &src, &tgt }) {
    bool changed;
    do {
      auto users = fn->getUsers();
      changed = false;

      for (auto bb : fn->getBBs()) {
        for (auto &i : bb->instrs()) {
          auto i_ptr = const_cast<Instr*>(&i);
          if (hasNoSideEffects(i) && !users.count(i_ptr))
            to_remove.emplace_back(i_ptr);
        }

        for (auto i : to_remove) {
          bb->delInstr(i);
          changed = true;
        }
        to_remove.clear();
      }

      changed |= fn->removeUnusedStuff(users);
    } while (changed);
  }

  // remove BBs not reachable from entry
  for (auto fn : { &src, &tgt }) {
    unordered_map<const BasicBlock*, bool> visited;
    vector<const BasicBlock*> visited_bbs;
    auto &entry = fn->getFirstBB();
    visited_bbs.push_back(&entry);

    // DFS to find reachable BBs
    unsigned size = visited_bbs.size();
    for (unsigned i = 0; i < size; ++i) {
      auto &bb = visited_bbs[i];
      auto &vis = visited[bb];
      if (vis)
        continue;
      vis = true;

      if (auto instr = dynamic_cast<const JumpInstr*>(&bb->back())) {
        auto tgt_it = const_cast<JumpInstr*>(instr)->targets();
        for (auto I = tgt_it.begin(), E = tgt_it.end(); I != E; ++I) {
          visited_bbs.push_back(&(*I));
          ++size;
        }
      }
    }

    // check if any bb was not reached before finding them
    vector<BasicBlock*> to_remove;
    if (visited.size() != fn->getBBs().size()) {
      for (auto bb : fn->getBBs()) {
        if (!visited[bb]) {
          // remove bb from phi instrs in its sucessors
          if (auto instr = dynamic_cast<JumpInstr*>(&bb->back())) {
            auto tgt_it = instr->targets();
            for (auto I = tgt_it.begin(), E = tgt_it.end(); I != E; ++I) {
              for (auto &instr : (*I).instrs()) {
                if (auto phi = dynamic_cast<const Phi*>(&instr))
                  const_cast<Phi&>(*phi).removeValue(bb->getName());
                else
                  break;
              }
            }
          }
          // delay removal until all phi's were processed
          to_remove.push_back(bb);
        }
      }
      // remove unreachable blocks
      for (auto bb : to_remove) {
        fn->removeBB(*bb);
      }
    }
  }

  auto k = unroll_factor;

  // DEBUG
  auto loops_so_far = 0;
  auto max_loops = -1;

  struct UnrollNodeData {
    unsigned id;
    // the bb from which id was duped
    unsigned original;
    // the original cfg this bb corresponds to before unroll
    unsigned first_original;
    // the bb in original CFG from which this has been duped
    unsigned dupe_counter;
    std::optional<unsigned> last_dupe;
    // id of loop in which this bb was last duped in
    optional<unsigned> prev_loop_dupe;
    bool pre_duped = false;
    // instructions that were duplicated given original and new in this bb
    vector<pair<Value*, Value*>> dupes;
    unsigned num_preds_changed_to_sink;
    // suffix for bb name
    string suffix;
  };

  if (k > 0) {
    // Loop unrolling
    for (auto fn : { &src, &tgt }) {
      CFG cfg(*fn);
      LoopTree lt(*fn, cfg);

      // skip if has no loops
      if (lt.loopCount() == 0)
        continue;

      vector<UnrollNodeData> unroll_data;
      unsigned cur_loop; // current loop being unrolled
      optional<unsigned> prev_loop; // loop unrolled before current
      // keep nodes that are inconsistent with topological order for fixing
      // after each loop unroll
      optional<unsigned> last_duped_header;
      unsigned num_duped_bbs = 0;
      optional<BasicBlock*> sink;

      // all dupes and the bb_id they were created for a given instr
      unordered_map<Value*, list<pair<unsigned, Value*>>> instr_dupes;

      // keep edges to merges to check for phis
      vector<tuple<unsigned, unsigned, bool>> merge_in_edges;

      // Prepare data structure for unroll algorithm
      for (auto node : lt.node_data) {
        unroll_data.emplace_back();
        auto &u_data = unroll_data.back();
        u_data.id = node.id;
        u_data.original = node.id;
        u_data.last_dupe = node.id;
        u_data.first_original = node.id;
      }

      // debug print cfg and loop tree
      if (config::debug) {
        if (fn == &tgt) continue;
        ofstream f1("src.dot");
        cfg.printDot(f1);
        ofstream f2("loop.dot");
        lt.printDot(f2);
      }

      auto last_dupe = [&](unsigned bb) -> unsigned {
        return *unroll_data[unroll_data[bb].original].last_dupe;
      };

      auto dupe_bb = [&](unsigned bb, unsigned header) -> unsigned {
        lt.node_data.reserve(lt.node_data.size()+1);
        auto &bb_data = lt.node_data[bb];
        bb_data.id = bb;

        unroll_data.emplace_back();
        auto &u_bb_data = unroll_data[bb];

        // get bb suffix
        auto &dupe_counter = unroll_data[u_bb_data.first_original].dupe_counter;
        auto bb_first_orig = lt.node_data[u_bb_data.first_original].bb;
        string suffix = "_#" + to_string(++dupe_counter);

        // dupe bb without instrs
        auto newbb = bb_first_orig->dup(suffix, false);
        auto ins_bb = fn->addBB(move(*newbb));

        auto id = lt.node_data.size();
        lt.bb_map[ins_bb] = id;

        // manually dupe instrs and update instr_dupes and unroll_data.dupes
        for (auto &i : bb_first_orig->instrs()) {
          ins_bb->addInstr(move(i.dup(suffix)));
          auto i_val = (Value*) &i;
          instr_dupes[i_val].emplace_back(id, &ins_bb->back());
          unroll_data[id].dupes.emplace_back(i_val, &ins_bb->back());
        }
        unroll_data[id].suffix = move(suffix);

        lt.node_data.emplace_back();
        if (id >= lt.loop_data.size())
          lt.loop_data.emplace_back();
        lt.loop_data[id].id = id;

        ((JumpInstr*) &ins_bb->back())->clearTargets();
        auto &ins_n_data = lt.node_data[id];
        ins_n_data.bb = ins_bb;
        ins_n_data.id = id;
        ins_n_data.header = bb_data.header;
        ins_n_data.first_header = *bb_data.first_header;

        auto &u_ins_data = unroll_data[id];

        // if bb was last duped in a different loop, make it the new original
        u_ins_data.original = u_bb_data.original;
        if (u_bb_data.prev_loop_dupe.has_value() &&
            u_bb_data.prev_loop_dupe != cur_loop) {
          u_ins_data.original = bb;
          u_bb_data.original = bb;
        }

        u_bb_data.prev_loop_dupe = cur_loop;
        u_ins_data.prev_loop_dupe = cur_loop;
        unroll_data[u_ins_data.original].last_dupe = id;
        u_ins_data.id = id;
        u_ins_data.first_original = u_bb_data.first_original;

        // add duped bbs straight into the containing loop's body if it exists
        auto &fh = lt.node_data[header].first_header;
        if (fh) {
          auto h_data = &lt.node_data[*fh];
          while (h_data->id != lt.ROOT_ID) {
            lt.loop_data[h_data->id].nodes.push_back(id);
            h_data = &lt.node_data[*h_data->first_header];
          }
        }

        ++num_duped_bbs;
        return id;
      };

      auto in_loop = [&](unsigned bb, unsigned loop_header) -> bool {
        if (bb == loop_header) return true;
        auto bb_header = *lt.node_data[bb].first_header;

        while (bb_header) {
          if (bb_header != loop_header)
            bb_header = *lt.node_data[bb_header].first_header;
          else
            return true;
        }

        return false;
      };

      auto is_back_edge = [&](unsigned src, unsigned dst) -> bool {
        auto &src_succs = lt.node_data[src].succs;
        auto I = src_succs.find(dst);
        return I != src_succs.end() ? I->second.second : false;
      };

      auto add_edge = [&](Value *cond, unsigned src, unsigned dst, bool replace,
                          bool as_back) {
        auto &src_data = lt.node_data[src];
        auto instr = (JumpInstr*) &src_data.bb->back();
        bool replaced = false;

        if (replace) {
          replaced = instr->replaceTarget(cond, *lt.node_data[dst].bb);
          if (replaced) {
            auto &succs = lt.node_data[src].succs;
            for (auto &[succ, data] : succs) {
              if (data.first == cond) {
                data.second = as_back;
                auto node_handler = lt.node_data[src].succs.extract(succ);
                node_handler.key() = dst;
                lt.node_data[src].succs.insert(move(node_handler));
                // TODO erase src from old_succ.preds without iterator
                // invalidation
                break;
              }
            }
            lt.node_data[dst].preds.emplace_back(cond, src);
          }
        }

        if (!replace || !replaced) {
          if (as_back && !sink)
            sink = &fn->getBB("#sink");
          auto dst_ = as_back ? *sink : lt.node_data[dst].bb;
          instr->addTarget(cond, *dst_);
          lt.node_data[dst].preds.emplace_back(cond, src);
          lt.node_data[src].succs.emplace(dst, make_pair(cond, as_back));
        }

        // keep edge for checking phi entries
        if (!replace || replaced) {
          auto &num_preds_sink = unroll_data[dst].num_preds_changed_to_sink;
          if (as_back)
            ++num_preds_sink;
          auto non_sink_preds = lt.node_data[dst].preds.size() - num_preds_sink;
          auto &dst_d = lt.node_data[dst];
          if (!as_back) {
            auto &fi = dst_d.bb->front();
            if (non_sink_preds > 1 || dynamic_cast<Phi*>(&fi))
              merge_in_edges.emplace_back(src, dst, non_sink_preds == 2);
          }
        }
      };

      auto duplicate_header = [&](unsigned header, unsigned n, bool last_it)
                                  -> optional<unsigned> {
        optional<unsigned> duped_header;

        // return empty if duped header will have no outgoing edges
        if (last_it) {
          bool edge_will_be_added = false;
          for (auto &[dst, data] : lt.node_data[header].succs)
            if (!in_loop(dst, header))
              edge_will_be_added = true;
          if (!edge_will_be_added)
            return duped_header;
        }

        duped_header = dupe_bb(header, n);
        auto &duped_header_data = lt.node_data[*duped_header];
        ((JumpInstr*) &duped_header_data.bb->back())->clearTargets();

        if (last_it) {
          // back-edges as edges to #sink
          for (auto &[dst, data] : lt.node_data[header].succs) {
            if (in_loop(dst, header))
              add_edge(data.first, *duped_header, last_dupe(dst), false, true);
          }
        }

        return duped_header;
      };

      auto duplicate_body = [&]() {
        unsigned loop_size = lt.loop_data[cur_loop].nodes.size();
        lt.loop_data.reserve(lt.loop_data.size()+loop_size);
        auto &loop = lt.loop_data[cur_loop];
        loop_size = loop.nodes.size();
        for (unsigned i = 1; i < loop_size; ++i)
          dupe_bb(loop.nodes[i], cur_loop);
      };

      vector<bool> visited;
      stack<unsigned> S;
      S.push(0);
      visited.resize(lt.loop_data.size());

      while (!S.empty()) {
        auto n = S.top();
        S.pop();

        if (!visited[n]) {
          visited[n] = true;
          S.push(n);
          for (auto child_loop : lt.loop_data[n].child_loops)
            S.push(child_loop);
        } else {
          cur_loop = n;
          if ((int) loops_so_far == max_loops) continue;
          ++loops_so_far;

          // ignore loops not marked reducible or irreducible
          auto n_type = lt.node_data[n].type;
          if (n_type != LoopTree::LHeaderType::reducible &&
              n_type != LoopTree::LHeaderType::irreducible)
            continue;

          // pre-dupe all headers of loops that contain this one if not done yet
          // in outer -> inner order
          stack<unsigned> loops;
          auto loop = n;
          while (loop != lt.ROOT_ID && !unroll_data[loop].pre_duped) {
            loops.push(loop);
            loop = *lt.node_data[loop].first_header;
          }

          while (!loops.empty()) {
            loop = loops.top();
            loops.pop();
            unroll_data[loop].pre_duped = true;

            auto hdr = duplicate_header(loop, loop, k == 1);
            if (!hdr)
              break;

            for (auto &[c, pred] : lt.node_data[loop].preds) {
              if (in_loop(pred, loop))
                add_edge(c, pred, *hdr, is_back_edge(pred, loop), false);
            }

            for (auto &[dst, data] : lt.node_data[loop].succs) {
              if (!in_loop(dst, loop))
                add_edge(data.first, *hdr, last_dupe(dst), false, false);
            }
          }

          auto n_prev = last_dupe(n);
          for (unsigned i = 1; i < k; ++i) {
            // create BB copies of the loop body and header
            duplicate_body();
            auto n_ = duplicate_header(n, n, i == k - 1);

            // dupe body edges
            auto &loop = lt.loop_data[n].nodes;
            auto loop_size = loop.size();
            for (unsigned i = 1; i < loop_size; ++i) {
              auto bb = loop[i];
              for (auto &[dst, data] : lt.node_data[bb].succs) {
                bool dst_in_loop = in_loop(unroll_data[dst].original, cur_loop);
                auto dst_ = dst_in_loop ? last_dupe(dst) : dst;
                bool back_edge = is_back_edge(bb, dst);
                add_edge(data.first, last_dupe(bb), dst_, back_edge, back_edge);
              }
            }

            // dupe header edges
            for (auto &[dst, data] : lt.node_data[n].succs) {
              if (in_loop(dst, n))
                add_edge(data.first, n_prev, last_dupe(dst), false, false);
              else
                if (n_)
                  add_edge(data.first, *n_, dst, false, false);

            }
            n_prev = *n_;
          }
          prev_loop = cur_loop;
        }
      }

      // topsort in sort.h but specific to the data structures here + iterative
      // also build new preorder + last numbering
      lt.last.clear();
      lt.number.clear();
      lt.nodes.clear();
      lt.last.resize(lt.node_data.size());
      lt.number.resize(lt.node_data.size());
      lt.nodes.resize(lt.node_data.size());

      unsigned current = 0;
      if (num_duped_bbs > 0) {
        vector<unsigned> sorted;
        vector<unsigned> worklist;
        vector<pair<bool, bool>> marked; // <visited, pushed>
        marked.resize(lt.node_data.size());
        worklist.push_back(lt.ROOT_ID);

        while (!worklist.empty()) {
          auto cur = worklist.back();
          auto &[seen, pushed] = marked[cur];
          worklist.pop_back();

          if (!seen) {
            seen = true;
            lt.nodes[current] = cur;
            lt.number[cur] = current++;
            worklist.push_back(cur);
            for (auto child : lt.node_data[cur].succs)
              if (!child.second.second && !marked[child.first].first)
                worklist.push_back(child.first);
          } else {
            if (!pushed) {
              lt.last[lt.number[cur]] = current - 1;
              sorted.emplace_back(cur);
              pushed = true;
            }
          }
        }

        // update BB_order in function for the desired topological order
        auto &bbs = fn->getBBs();
        bbs.clear();
        for (auto I = sorted.rbegin(), E = sorted.rend(); I != E; ++I)
          bbs.emplace_back(lt.node_data[*I].bb);

        // check if a_id is ancestor of b_id
        // credit to paper & authors:
        // Havlak, Paul (1997). Nesting of Reducible and Irreducible Loops.
        auto isAncestor = [&](unsigned a_id, unsigned b_id) -> bool {
          auto a_num = lt.number[a_id];
          auto b_num = lt.number[b_id];
          return a_num <= b_num && b_num <= lt.last[a_num];
        };

        // update phi entries and add phi instructions when necessary
        visited.clear();
        visited.resize(lt.node_data.size());
        unordered_map<Value*, Value*> phi_use;

        // check if necessary to add phi instructions
        for (auto [pred, target, became_merge] : merge_in_edges) {
          if (visited[target])
            continue;
          visited[target] = true;

          auto &target_data = lt.node_data[target];
          unordered_set<Value*> seen_uses;

          vector<unique_ptr<Phi>> to_insert;
          if (became_merge) { // check for new phi instrs only when became merge
            for (auto &instr : target_data.bb->instrs()) {
              for (auto use : instr.operands()) {
                if (dynamic_cast<Constant*>(use))
                  continue;
                // avoid checking same use twice
                if (seen_uses.find(use) != seen_uses.end())
                  continue;
                seen_uses.insert(use);
                auto first_pred = target_data.preds.front().second;

                // check for each pred if use was duped on path to pred
                for (auto pred : target_data.preds) {
                  if (pred.second == first_pred)
                    continue;

                  auto &use_dupes = instr_dupes[use];
                  unsigned i = 0;
                  bool added_phi = false;

                  for (auto I = use_dupes.begin(), E = use_dupes.end(); I != E;
                       ++I) {
                    auto [use_dupe_bb_id, val] = *I;

                    if (isAncestor(use_dupe_bb_id, pred.second) &&
                        !isAncestor(use_dupe_bb_id, first_pred)) {
                      auto &sfx = unroll_data[target].suffix;
                      auto phi = make_unique<Phi>(use->getType(),
                                                  use->getName() + sfx + "phi");
                      to_insert.push_back(move(phi));
                      auto &phi_ = to_insert.back();
                      use_dupes.emplace(++I, target, &(*phi_));
                      phi_use[&(*phi_)] = use;
                      added_phi = true;
                      break;
                    }
                    ++i;
                  }
                  if (added_phi)
                    break;
                }
              }
            }
          }

          for (auto &phi : to_insert)
            target_data.bb->addInstrFront(move(phi));

          // helper func to get latest Value* 'val' in merge for its pred 'pred'
          function<optional<Value*>(unsigned, Value*)> get_updated_val_for_pred;
          get_updated_val_for_pred = [&](unsigned pred, Value* use) {
            optional<Value*> val;
            auto &dupes = instr_dupes[use];
            for (auto I = dupes.begin(), E = dupes.end(); I != E; ++I) {
              auto id = I->first;
              if (!isAncestor(id, pred) && I != dupes.begin()) {
                val = (--I)->second;
                break;
              }
            }
            return val;
          };

          // phi entries
          for (auto &instr : target_data.bb->instrs()) {
            if (auto phi = dynamic_cast<Phi*>(const_cast<Instr*>(&instr))) {
              auto no_entries = phi->operands().empty();
              auto use = no_entries ? phi_use[phi] : phi->operands().front();
              // TODO does it make sense to test first phi op as constant only?
              if (dynamic_cast<Constant*>(use))
                  continue;

              // remove entries that are no longer predecessors
              // n: you do want to remove without first_original, and then add new
              unordered_set<unsigned> preds;
              unordered_map<unsigned, pair<Value*, bool>> seen_entries;
              for (auto pred : target_data.preds)
                preds.insert(pred.second);
              for (auto &[val, bb_name] : phi->getValues()) {
                auto pred = lt.bb_map[&fn->getBB(bb_name)];
                auto &seen_entry = seen_entries[pred];
                seen_entry.first = val;
                if (preds.find(pred) == preds.end()) {
                  phi->removeValue(bb_name);
                  seen_entry.second = true;
                }
              }

              // add entries
              for (auto &pred : target_data.preds) {
                auto original_pred = unroll_data[pred.second].first_original;
                auto [val, removed] = seen_entries[original_pred];
                auto u_val = get_updated_val_for_pred(pred.second, val);
                if (u_val) {
                  auto name = lt.node_data[pred.second].bb->getName();
                  phi->addValue(**u_val, move(name));
                }
              }
            } else {
              break;
            }
          }
        }

        // update instruction operands by traversing bb's in reverse preorder
        auto users = fn->getUsers();
        for (int i = lt.nodes.size() - 1; i > -1; --i) {
          for (auto &i_dupe : unroll_data[lt.nodes[i]].dupes) {
            auto its = users.equal_range(i_dupe.first);

            for (auto I = its.first, E = its.second; I != E; ++I) {
              auto instr = (Instr*) I->second;
              if (dynamic_cast<Phi*>(instr))
                continue;

              // if dupe of declaration is ancestor of use then replace
              auto containing_bb = *instr->containingBB();
              int c_bb_id = lt.bb_map[containing_bb];
              if (isAncestor(lt.nodes[i], c_bb_id)) {
                // if same bb, verify use comes after declaration
                auto what = I->first;
                auto with = (Value*) i_dupe.second;
                bool use_before_decl = false;
                if (lt.nodes[i] == c_bb_id) {
                  for (auto &instr : containing_bb->instrs()) {
                    if (&instr == with)
                      break;
                    if (&instr == what) {
                      use_before_decl = true;
                      break;
                    }
                  }
                }
                if (!use_before_decl)
                  instr->rauw(*what, *with);
              }
            }
          }
        }
      }

      // DEBUG , print unrolled dot for src only
      if (config::debug) {
        if (fn == &tgt) continue;
        CFG cfg_(*fn);
        ofstream f3("src_unrolled.dot");
        cfg_.printDot(f3);
      }
    }
  }
}

void Transform::print(ostream &os, const TransformPrintOpts &opt) const {
  os << "\n----------------------------------------\n";
  if (!name.empty())
    os << "Name: " << name << '\n';
  if (precondition) {
    precondition->print(os << "Pre: ");
    os << '\n';
  }
  src.print(os, opt.print_fn_header);
  os << "=>\n";
  tgt.print(os, opt.print_fn_header);
}

ostream& operator<<(ostream &os, const Transform &t) {
  t.print(os, {});
  return os;
}

}
