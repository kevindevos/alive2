// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/function.h"
#include "ir/instr.h"
#include "util/errors.h"
#include <stack>

using namespace smt;
using namespace util;
using namespace std;

namespace IR {

expr BasicBlock::getTypeConstraints(const Function &f) const {
  expr t(true);
  for (auto &i : instrs()) {
    t &= i.getTypeConstraints(f);
  }
  return t;
}

void BasicBlock::fixupTypes(const Model &m) {
  for (auto &i : m_instrs) {
    i->fixupTypes(m);
  }
}

void BasicBlock::addInstr(unique_ptr<Instr> &&i) {
  m_instrs.push_back(move(i));
}

void BasicBlock::delInstr(Instr *i) {
  for (auto I = m_instrs.begin(), E = m_instrs.end(); I != E; ++I) {
    if (I->get() == i) {
      m_instrs.erase(I);
      return;
    }
  }
}

unique_ptr<BasicBlock> BasicBlock::dup(const string &suffix) const {
  auto newbb = make_unique<BasicBlock>(name + suffix);
  for (auto &i : instrs()) {
    newbb->addInstr(i.dup(suffix));
  }
  return newbb;
}

ostream& operator<<(ostream &os, const BasicBlock &bb) {
  if (!bb.name.empty())
    os << bb.name << ":\n";
  for (auto &i : bb.instrs()) {
    os << "  ";
    i.print(os);
    os << '\n';
  }
  return os;
}


expr Function::getTypeConstraints() const {
  expr t(true);
  for (auto bb : getBBs()) {
    t &= bb->getTypeConstraints(*this);
  }
  for (auto &l : { getConstants(), getInputs(), getUndefs() }) {
    for (auto &v : l) {
      t &= v.getTypeConstraints();
    }
  }
  return t;
}

void Function::fixupTypes(const Model &m) {
  for (auto bb : getBBs()) {
    bb->fixupTypes(m);
  }
  for (auto &l : { getConstants(), getInputs(), getUndefs() }) {
    for (auto &v : l) {
      const_cast<Value&>(v).fixupTypes(m);
    }
  }
}

BasicBlock& Function::getBB(string_view name, bool push_front) {
  auto p = BBs.try_emplace(string(name), name);
  if (p.second) {
    if (push_front)
      BB_order.insert(BB_order.begin(), &p.first->second);
    else
      BB_order.push_back(&p.first->second);
  }
  return p.first->second;
}

const BasicBlock& Function::getBB(string_view name) const {
  return BBs.at(string(name));
}

const BasicBlock* Function::getBBIfExists(std::string_view name) const {
  auto I = BBs.find(string(name));
  return I != BBs.end() ? &I->second : nullptr;
}

void Function::removeBB(BasicBlock &BB) {
  BBs.erase(BB.getName());

  for (auto I = BB_order.begin(), E = BB_order.end(); I != E; ++I) {
    if (*I == &BB) {
      BB_order.erase(I);
      break;
    }
  }
}

void Function::addConstant(unique_ptr<Value> &&c) {
  constants.emplace_back(move(c));
}

vector<GlobalVariable *> Function::getGlobalVars() const {
  vector<GlobalVariable *> gvs;
  for (auto I = constants.begin(), E = constants.end(); I != E; ++I) {
    if (auto *gv = dynamic_cast<GlobalVariable*>(I->get()))
      gvs.push_back(gv);
  }
  return gvs;
}

vector<string_view> Function::getGlobalVarNames() const {
  vector<string_view> gvnames;
  auto gvs = getGlobalVars();
  transform(gvs.begin(), gvs.end(), back_inserter(gvnames),
            [](auto &itm) { return string_view(itm->getName()).substr(1); });
  return gvnames;
}

void Function::addPredicate(unique_ptr<Predicate> &&p) {
  predicates.emplace_back(move(p));
}

void Function::addUndef(unique_ptr<UndefValue> &&u) {
  undefs.emplace_back(move(u));
}

void Function::addAggregate(unique_ptr<AggregateValue> &&a) {
  aggregates.emplace_back(move(a));
}

void Function::addInput(unique_ptr<Value> &&i) {
  assert(dynamic_cast<Input *>(i.get()) ||
         dynamic_cast<ConstantInput*>(i.get()));
  inputs.emplace_back(move(i));
}

bool Function::hasReturn() const {
  for (auto &i : instrs()) {
    if (dynamic_cast<const Return *>(&i))
      return true;
  }
  return false;
}

void Function::syncDataWithSrc(const Function &src) {
  auto IS = src.inputs.begin(), ES = src.inputs.end();
  auto IT = inputs.begin(), ET = inputs.end();

  for (; IS != ES && IT != ET; ++IS, ++IT) {
    if (auto in_tgt = dynamic_cast<Input*>(IT->get()))
      in_tgt->copySMTName(*dynamic_cast<Input*>(IS->get()));

    if (!(IS->get()->getType() == IT->get()->getType()).isTrue())
      throw AliveException("Source and target args have different type", false);
  }

  if (IS != ES || IT != ET)
    throw AliveException("Source and target have different number of args",
                         false);
}

Function::instr_iterator::
instr_iterator(vector<BasicBlock*>::const_iterator &&BBI,
               vector<BasicBlock*>::const_iterator &&BBE)
  : BBI(move(BBI)), BBE(move(BBE)) {
  next_bb();
}

void Function::instr_iterator::next_bb() {
  if (BBI != BBE) {
    auto BB_instrs = (*BBI)->instrs();
    II = BB_instrs.begin();
    IE = BB_instrs.end();
  }
}

void Function::instr_iterator::operator++(void) {
  if (++II != IE)
    return;
  ++BBI;
  next_bb();
}

multimap<Value*, Value*> Function::getUsers() const {
  multimap<Value*, Value*> users;
  for (auto &i : instrs()) {
    for (auto op : i.operands()) {
      users.emplace(op, const_cast<Instr*>(&i));
    }
  }
  for (auto &agg : aggregates) {
    for (auto val : agg->getVals()) {
      users.emplace(val, agg.get());
    }
  }
  for (auto &c : constants) {
    if (auto agg = dynamic_cast<AggregateValue*>(c.get())) {
      for (auto val : agg->getVals()) {
        users.emplace(val, agg);
      }
    }
  }
  return users;
}

template <typename T>
static bool removeUnused(T &data, const multimap<Value*, Value*> &users) {
  bool changed = false;
  for (auto I = data.begin(); I != data.end(); ) {
    if (users.count(I->get())) {
      ++I;
    } else {
      I = data.erase(I);
      changed = true;
    }
  }
  return changed;
}

bool Function::removeUnusedStuff(const multimap<Value*, Value*> &users) {
  bool changed = removeUnused(aggregates, users);
  changed |= removeUnused(constants, users);
  return changed;
}

void Function::print(ostream &os, bool print_header) const {
  {
    const auto &gvars = getGlobalVars();
    if (!gvars.empty()) {
      for (auto &v : gvars) {
        v->print(os);
        os << '\n';
      }
      os << '\n';
    }
  }

  if (print_header) {
    os << "define" << attrs << ' ' << getType() << " @" << name << '(';
    bool first = true;
    for (auto &input : getInputs()) {
      if (!first)
        os << ", ";
      os << input;
      first = false;
    }
    os << ") {\n";
  }

  bool first = true;
  for (auto bb : BB_order) {
    if (!first)
      os << '\n';
    os << *bb;
    first = false;
  }

  if (print_header)
    os << "}\n";
}

ostream& operator<<(ostream &os, const Function &f) {
  f.print(os);
  return os;
}


void CFG::edge_iterator::next() {
  // jump to next BB with a terminator that is a jump
  while (true) {
    if (bbi == bbe)
      return;

    if (auto instr = dynamic_cast<JumpInstr*>(&(*bbi)->back())) {
      ti = instr->targets().begin();
      te = instr->targets().end();
      return;
    }

    ++bbi;
  }
}

CFG::edge_iterator::edge_iterator(vector<BasicBlock*>::iterator &&it,
                                  vector<BasicBlock*>::iterator &&end)
  : bbi(move(it)), bbe(move(end)) {
  next();
}

tuple<const BasicBlock&, const BasicBlock&, const Instr&>
  CFG::edge_iterator::operator*() const {
  return { **bbi, *ti, (*bbi)->back() };
}

void CFG::edge_iterator::operator++(void) {
  if (++ti == te) {
    ++bbi;
    next();
  }
}

bool CFG::edge_iterator::operator!=(edge_iterator &rhs) const {
  return bbi != rhs.bbi && (bbi == bbe || rhs.bbi == rhs.bbe || ti != rhs.ti);
}

static string_view bb_dot_name(const string &name) {
  if (name[0] == '%')
    return string_view(name).substr(1);
  return name;
}

void CFG::printDot(ostream &os) const {
  os << "digraph {\n"
        "\"" << bb_dot_name(f.getBBs()[0]->getName()) << "\" [shape=box];\n";

  for (auto [src, dst, instr] : *this) {
    (void)instr;
    os << '"' << bb_dot_name(src.getName()) << "\" -> \""
       << bb_dot_name(dst.getName()) << "\";\n";
  }
  os << "}\n";
}

// Build a tree of loop headers and their nested loop headers
// Adaptation of the algorithm in the article
// Havlak, Paul (1997).
// Nesting of Reducible and Irreducible Loops.
void LoopTree::buildLoopTree() {
  vector<unsigned> nodes; // nodes indexed by preorder
  vector<unsigned> number; // preorder number for bb given id in bb_map
  vector<unsigned> last;
  vector<bool> visited;
  unordered_map<const BasicBlock*, unsigned> bb_map;
  
  // source -> target
  stack<const BasicBlock*> dfs_work_list;
  vector<Vecset*> vecsets;
  vector<Vecset> vecsets_data;
  vecsets_data.reserve(f.getBBs().size());

  auto bb_id = [&](const BasicBlock *bb) {
    auto [I, inserted] = bb_map.emplace(bb, nodes.size());
    if (inserted) {
      nodes.emplace_back();
      number.emplace_back();
      last.emplace_back();
      node_data.emplace_back();
      vecsets.emplace_back();
      vecsets_data.emplace_back();
      visited.emplace_back();
    }
    return I->second;
  };
  
  auto vecsetFind = [&](unsigned bb) {
    return vecsets[bb]->repr();
  };

  auto vecsetUnion = [&](unsigned from, unsigned to) {
    auto from_set = vecsets[from];
    auto to_set = vecsets[to];
    for (auto from_el : from_set->getAll()) {
      to_set->add(from_el);
      vecsets[from_el] = to_set;
    }
    from_set->clear();
  };
  
  // check ancestry by preorder number
  auto isAncestor = [&](unsigned w, unsigned v) {
    return w <= v && v <= last[w];
  };
  
  // DFS to establish node ordering
  unsigned START_BB_ID = 0;
  auto entry = &f.getFirstBB();
  dfs_work_list.push(entry);
  unsigned current = START_BB_ID;
  while (!dfs_work_list.empty()) {
    auto current_bb = dfs_work_list.top();
    dfs_work_list.pop();
    int n = bb_id(current_bb);
    nodes[current] = n;
    auto &cur_node_data = node_data[n];
    cur_node_data.bb = current_bb;
    
    if (!visited[n]) { // TODO can't use number as visited for id = 0 possible
      visited[n] = true;
      number[n] = current++;
      vecsets_data[n] = Vecset(n);
      vecsets[n] = &vecsets_data[n];
      dfs_work_list.push(current_bb);
      if (auto instr = dynamic_cast<const JumpInstr*>(&current_bb->back())) {
        auto tgt_it = const_cast<JumpInstr*>(instr)->targets();
        for (auto I = tgt_it.begin(), E = tgt_it.end(); I != E; ++I) {
          auto t_n = bb_id(&(*I));
          if (!visited[t_n]) {
            dfs_work_list.push(&(*I));
          }
          node_data[t_n].preds.insert(n);
        }
      }
    } else {
      last[number[n]] = current - 1;
    }
  }

  // fix_loops
  for (unsigned w_num = 0; w_num < nodes.size(); ++w_num) {
    auto &w = nodes[w_num];
    auto &w_data = node_data[w];
    for (auto &v : w_data.preds) {
      if (w_num <= number[v]) 
        w_data.red_back_in.push_back(v);
      else
        w_data.other_in.push_back(v);
    }
    if (!w_data.red_back_in.empty() && w_data.other_in.size() > 1) {
      auto &new_bb = new_bbs.emplace_back("#loop_"+w_data.bb->getName());
      auto new_num = bb_id(&new_bb);
      auto new_data = node_data[new_num];
      for (auto &v : w_data.other_in)
        new_data.preds.insert(v);
      w_data.preds.clear();
      w_data.preds.insert(new_num);
    }
  }

  // analyze_loops
  // b. distinguish between back edges and non back edges
  unsigned nodes_size = nodes.size();
  for (unsigned w_num = 0; w_num < nodes_size; ++w_num) {
    auto &w = nodes[w_num];
    auto &w_data = node_data[w];
    w_data.header = 0;
    w_data.type = LHeaderType::nonheader;
    for (auto &v : w_data.preds) {
      if (isAncestor(w_num, number[v]))
        w_data.back_preds.push_back(v);
      else
        w_data.non_back_preds.push_back(v);
    }
  }

  // c. d. e. core of the algorithm
  node_data[0].header = 0;
  unordered_set<unsigned> P;
  stack<unsigned> work_list;
  for (unsigned w_num = nodes_size - 1; ; --w_num) {
    auto &w = nodes[w_num];
    P.clear();
    auto &w_data = node_data[w];
    for (auto &v : w_data.back_preds) {
      if (v != w) {
        auto v_repr = vecsetFind(v);
        P.insert(v_repr);
        work_list.push(v_repr);
      } else {
        w_data.type = LHeaderType::self;
      }
    }
    if (!P.empty())
      w_data.type = LHeaderType::reducible;
    while (!work_list.empty()) {
      auto x = work_list.top();
      work_list.pop();
      for (auto &y : node_data[x].non_back_preds) {
        unsigned y_ = vecsetFind(y);
        if (!isAncestor(w_num, number[y_])) {
          w_data.type = LHeaderType::irreducible;
          w_data.non_back_preds.push_back(y_);
        } else if (!P.count(y_) && y_ != w) {
          P.insert(y_);
          work_list.push(y_);
        }
      }
    }
    for (auto x : P) {
      node_data[x].header = w;
      vecsetUnion(x, w);
    }
     // terminate for loop with descending unsigned index without underflow
    if (!w_num)
      break;
  }
}

void LoopTree::printDot(std::ostream &os) const {
  os << "digraph {\n";

  for (auto node : node_data) {
    if (node.bb == &f.getFirstBB() || node.back_preds.empty())
      continue;
    
    auto header_bb = node_data[node.header].bb;
    if (header_bb == &f.getFirstBB()) {
      os << '"' << bb_dot_name(node.bb->getName()) << "\" [shape=box];\n";
    } else {
      os << '"' << bb_dot_name(node.bb->getName()) << "\" [shape=oval];\n";
      os << '"' << bb_dot_name(header_bb->getName()) << "\" -> \""
         << bb_dot_name(node.bb->getName()) << "\";\n";
    }
  }
 
  os << "}\n";
}

// Relies on Alive's top_sort run during llvm2alive conversion in order to
// traverse the cfg in reverse postorder to build dominators.
void DomTree::buildDominators() {
  unordered_set<const BasicBlock*> visited_src;

  // initialization
  unsigned i = f.getBBs().size();
  for (auto &b : f.getBBs()) {
    doms.emplace(b, *b).first->second.order = --i;
  }

  // build predecessors relationship
  for (const auto &[src, tgt, instr] : cfg) {
    (void)instr;
    // skip back-edges
    visited_src.insert(&src);
    if (!visited_src.count(&tgt))
      doms.at(&tgt).preds.push_back(&doms.at(&src));
  }

  // make sure all tree roots have themselves as dominator
  for (auto &[b, b_dom] : doms) {
    (void)b;
    if (b_dom.preds.empty())
      b_dom.dominator = &b_dom;
  }

  // Adaptation of the algorithm in the article
  // Cooper, Keith D.; Harvey, Timothy J.; and Kennedy, Ken (2001). 
  // A Simple, Fast Dominance Algorithm
  // http://www.cs.rice.edu/~keith/EMBED/dom.pdf
  // Makes multiple passes when CFG is cyclic to update incorrect initial
  // dominator guesses.
  bool changed;
  do {
    changed = false;
    for (auto &b : f.getBBs()) {
      auto &b_node = doms.at(b);
      if (b_node.preds.empty())
        continue;
      
      auto new_idom = b_node.preds.front();
      for (auto p : b_node.preds) {
        if (p->dominator != nullptr) {
          new_idom = intersect(p, new_idom);
        }
      }

      if (b_node.dominator != new_idom) {
        b_node.dominator = new_idom;
        changed = true;
      }
    }
  } while (changed);
}

DomTree::DomTreeNode* DomTree::intersect(DomTreeNode *f1, DomTreeNode *f2) {
  auto f1_start = f1, f2_start = f2;

  while (f1->order != f2->order) {
    // if f1 and f2 reached diferent tree roots, then no common parent exists
    // therefore no "dominator" exists
    // as a convention, return the node of the tree with root at entry in these
    // cases, dom trees for subtrees not rooted at entry will be wrong
    if (f1 == f1->dominator && f2 == f2->dominator)
      return &f1->bb == &f.getFirstBB() ? f1_start : f2_start;
    while (f1->order < f2->order && f1 != f1->dominator)
      f1 = f1->dominator;
    while (f2->order < f1->order && f2 != f2->dominator)
      f2 = f2->dominator;
  }
  return f1;
}

// get immediate dominator BasicBlock
const BasicBlock* DomTree::getIDominator(const BasicBlock &bb) const {
  auto dom = doms.at(&bb).dominator;
  return dom ? &dom->bb : nullptr;
}

void DomTree::printDot(std::ostream &os) const {
  os << "digraph {\n"
        "\"" << bb_dot_name(f.getBBs()[0]->getName()) << "\" [shape=box];\n";

  for (auto I = f.getBBs().begin()+1, E = f.getBBs().end(); I != E; ++I) {
    if (auto dom = getIDominator(**I)) {
      os << '"' << bb_dot_name(dom->getName()) << "\" -> \""
         << bb_dot_name((*I)->getName()) << "\";\n";
    }
  }

  os << "}\n";
}

} 

