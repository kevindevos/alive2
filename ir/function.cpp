// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "ir/function.h"
#include "ir/instr.h"
#include "util/errors.h"
#include <stack>
#include <iostream>

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
  auto &i_bb = i->containingBB();
  i_bb = this;
  m_instrs.push_back(move(i));
}

void BasicBlock::addInstrFront(unique_ptr<Instr> &&i) {
  auto &i_bb = i->containingBB();
  i_bb = this;
  m_instrs.insert(m_instrs.begin(), move(i));
}


unique_ptr<Instr> BasicBlock::delInstr(Instr *i) {
  unique_ptr<Instr> ret;
  for (auto I = m_instrs.begin(), E = m_instrs.end(); I != E; ++I) {
    if (&(**I) == i) {
      i->containingBB().reset();
      ret = move(*I);
      m_instrs.erase(I);
    }
  }
  return ret;
}

unique_ptr<BasicBlock> BasicBlock::dup(const string &suffix,
                                       bool with_instrs = true) const {
  auto newbb = make_unique<BasicBlock>(name + suffix);
  if (with_instrs)
    for (auto &i : instrs())
      newbb->addInstr(i.dup(suffix));
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

BasicBlock* Function::addBB(BasicBlock &&bb) {
  auto [b, inserted] = BBs.emplace(bb.getName(), move(bb));
  BB_order.push_back(&b->second);
  return &b->second;
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
static bool removeUnused(T &data, const multimap<Value*, Value*> &users,
                         const vector<string_view> &src_glbs) {
  bool changed = false;
  for (auto I = data.begin(); I != data.end(); ) {
    if (users.count(I->get())) {
      ++I;
      continue;
    }

    // don't delete glbs in target that are used in src
    if (auto gv = dynamic_cast<GlobalVariable*>(I->get())) {
      auto name = string_view(gv->getName()).substr(1);
      if (find(src_glbs.begin(), src_glbs.end(), name) != src_glbs.end()) {
        ++I;
        continue;
      }
    }

    I = data.erase(I);
    changed = true;
  }
  return changed;
}

bool Function::removeUnusedStuff(const multimap<Value*, Value*> &users,
                                 const vector<string_view> &src_glbs) {
  bool changed = removeUnused(aggregates, users, src_glbs);
  changed |= removeUnused(constants, users, src_glbs);
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

    if (!(*bbi)->empty()) {
      if (auto instr = dynamic_cast<JumpInstr*>(&(*bbi)->back())) {
        ti = instr->targets().begin();
        te = instr->targets().end();
        return;
      }
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

// Get the representative of the set that presently contains basicblock bb
unsigned LoopTree::vecsetFind(unsigned bb) {
  return vecsets[bb]->repr();
}

// Move all elements in from set into to set, and clear from set
void LoopTree::vecsetUnion(unsigned from, unsigned to) {
  auto from_set = vecsets[from];
  auto to_set = vecsets[to];
  for (auto from_el : from_set->getAll()) {
    to_set->add(from_el);
    vecsets[from_el] = to_set;
  }
  from_set->clear();
}

// Build a tree of loop headers and their nested loop headers
// Adaptation of the algorithm in the article
// Havlak, Paul (1997).
// Nesting of Reducible and Irreducible Loops.
void LoopTree::buildLoopTree() {
  vector<bool> visited; // bb id -> visited

  auto sz = f.getBBs().size();
  nodes.resize(sz+1);
  number.resize(sz);
  last.resize(sz);
  node_data.resize(sz);
  vecsets.resize(sz);
  vecsets_data.resize(sz);
  visited.resize(sz);

  // generate bb ids
  unsigned i = 0;
  for (auto bb : f.getBBs()) {
    node_data[i].bb = bb;
    bb_map.emplace(bb, i++);
  }

  // topsort before DFS
  vector<unsigned> sorted;
  vector<unsigned> marked;
  vector<unsigned> pushed;
  vector<unsigned> top_order_idx;
  vector<const BasicBlock*> wl;
  marked.resize(sz);
  pushed.resize(sz);
  top_order_idx.resize(sz);

  wl.emplace_back(&f.getFirstBB());
  while (!wl.empty()) {
    auto cur = wl.back();
    auto cur_id = bb_map[cur];
    wl.pop_back();
    auto &vis = marked[cur_id];

    if (!vis) {
      vis = true;
      wl.emplace_back(cur);
      if (auto instr = dynamic_cast<const JumpInstr*>(&cur->back())) {
        auto tgt_it = const_cast<JumpInstr*>(instr)->targets();
        for (auto I = tgt_it.begin(), E = tgt_it.end(); I != E; ++I)
          wl.emplace_back(&(*I));
      }
    } else {
      if (!pushed[cur_id]) {
        sorted.emplace_back(cur_id);
        pushed[cur_id] = true;
      }
    }
  }

  // build top_order_idx
  for (unsigned i = sorted.size()-1, j = 0; i != -1u; --i, ++j)
    top_order_idx[sorted[i]] = j;


  // check if bb with preorder w is an ancestor of bb with preorder v
  auto isAncestor = [&](unsigned w, unsigned v) {
    return w <= v && v <= last[w];
  };

  // DFS to establish node ordering
  auto DFS = [&]() {
    stack<const BasicBlock*> dfs_work_list;

    auto entry = &f.getFirstBB();
    dfs_work_list.push(entry);
    unsigned current = ROOT_ID;

    auto try_push_worklist = [&](const BasicBlock *bb, unsigned pred, auto c,
                                 bool is_default) {
      auto t_n = bb_map[bb];
      bool b_visited = visited[t_n];
      if (!b_visited)
        dfs_work_list.push(bb);
      auto &t_data = node_data[t_n];
      t_data.id = t_n;
      // set back-edge flag to false for now, update later with DFS and
      // isAncestor
      t_data.preds.emplace_back(pred, c, false, is_default);
      node_data[pred].succs.emplace_back(t_n, c, false, is_default);
    };

    while (!dfs_work_list.empty()) {
      auto cur_bb = dfs_work_list.top();
      dfs_work_list.pop();
      int n = bb_map[cur_bb];
      nodes[current] = n;
      auto &cur_node_data = node_data[n];
      cur_node_data.bb = const_cast<BasicBlock*>(cur_bb);

      if (!visited[n]) {
        visited[n] = true;
        number[n] = current++;
        vecsets_data[n] = Vecset(n);
        vecsets[n] = &vecsets_data[n];
        dfs_work_list.push(cur_bb);

        // add sucessors to work_list if not visited in reverse topological ordr
        // to avoid classifying forward edges as backedges
        // <dst_id, dst bb, pred_id, cond, is_default, added>
        vector<tuple<unsigned, BasicBlock*, unsigned, Value*, bool, bool>> tgts;
        vector<unsigned> sorted_tgts; // tgts idx

        if (auto instr = dynamic_cast<const JumpInstr*>(&cur_bb->back())) {
          auto tgt_it = const_cast<JumpInstr*>(instr)->targets();
          auto first_it = true;
          for (auto I = tgt_it.begin(), E = tgt_it.end(); I != E; ++I) {
            auto [cond, bb] = I.get();
            bool is_default = dynamic_cast<const Switch*>(instr) && first_it;
            tgts.emplace_back(bb_map[bb], bb, n, cond, is_default, false);
            first_it = false;
          }
          // sort targets with descending topological order // TODO inefficient
          auto tgts_sz = tgts.size();
          optional<unsigned> max_top_order;
          optional<unsigned> max_tgts_idx;
          for (unsigned i = 0; i < tgts_sz; ++i) {
            for (unsigned j = 0; j < tgts_sz; ++j) {
              auto added = get<5>(tgts[j]);
              if (added)
                continue;
              auto j_top_order = top_order_idx[get<0>(tgts[j])];
              if (!max_top_order || j_top_order > *max_top_order) {
                max_top_order = j_top_order;
                max_tgts_idx = j;
              }
            }
            sorted_tgts.emplace_back(*max_tgts_idx);
            get<5>(tgts[*max_tgts_idx]) = true;
            max_top_order.reset();
            max_tgts_idx.reset();
          }
          // add to worklist in descending topological order
          // last is picked first
          for (auto idx : sorted_tgts) {
            auto &e = tgts[idx];
            try_push_worklist(get<1>(e), get<2>(e), get<3>(e), get<4>(e));
          }

        }
        tgts.clear();
        sorted_tgts.clear();
      } else {
        last[number[n]] = current - 1;
      }
    }
  };

  // Run DFS to build preorder numbering and the vecsets for analyze_loops
  DFS();

  // analyze_loops
  // b. distinguish between back edges and non back edges
  unsigned nodes_size = nodes.size();
  loop_data.resize(nodes_size);
  for (unsigned w_num = 0; w_num < nodes_size; ++w_num) {
    auto &w = nodes[w_num];
    loop_data[w].id = w;
    auto &w_data = node_data[w];
    w_data.header = 0;
    w_data.type = LHeaderType::nonheader;
    for (auto &pred : w_data.preds) {
      auto v = get<0>(pred);
      if (isAncestor(w_num, number[v]))
        w_data.back_preds.push_back(v);
      else
        w_data.non_back_preds.push_back(v);
    }
  }

  // c. d. e.
  // for each node with incoming reducible backedge, builds a set of bbs
  // that represents the loop, sets the loop header and type
  node_data[0].header = 0;
  unordered_set<unsigned> P;
  stack<unsigned> work_list;
  vector<unsigned> loops_with_new_bb;
  for (unsigned w_num = nodes_size - 1; ; --w_num) {
    auto w = (unsigned) nodes[w_num];
    P.clear();
    auto &w_data = node_data[w];
    auto &w_loop_data = loop_data[w];

    for (auto v : w_data.back_preds) {
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
        } else if (y_ != w) {
          if (P.insert(y_).second)
            work_list.push(y_);
        }
      }
    }

    if (!P.empty()) {
      // Union x into w regardless of valid loop or not, if not it will be in
      // a possible valid containing loop
      for (auto x : P) {
        vecsetUnion(x, w);
        node_data[x].header = w;
      }

      bool valid_loop = true;
      bool has_out_exit, has_out_entry, has_in_entry, has_in_exit;
      (void)has_out_exit;
      for (auto lnode : vecsets[w]->getAll()) {
        has_out_exit = has_out_entry = has_in_entry = has_in_exit = false;
        auto &lnode_data = node_data[lnode];

        for (auto &pred_ : lnode_data.preds) {
          auto pred = get<0>(pred_);
          if (vecsetFind(pred) != w)
            has_out_entry = true; // (x, lnode) : x not in loop
          else
            has_in_entry = true; // (x, lnode) : x in loop
        }

        for (auto &succ : lnode_data.succs) {
          if (vecsetFind(get<0>(succ)) != w)
            has_out_exit = true; // (lnode, x) : x not in loop
          else
            has_in_exit = true; // (lnode, x) : x in loop
        }

        // check if it is a valid loop header
        if (has_out_entry && has_in_entry && has_in_exit) {
          if (lnode != w)
            w_loop_data.alternate_headers.push_back(lnode);
        } else {
          // if chosen header is invalid do not keep this loop
          if (lnode == w) {
            valid_loop = false;
            lnode_data.type = LHeaderType::nonheader;
            break;
          }
        }

        // if a node "in" the loop has no outgoing edge into another node
        // in this loop or no incoming edge from a node in the loop,
        // then it is not part of the loop
        if (has_in_exit && has_in_entry) {
          w_loop_data.nodes.push_back(lnode);
          if (lnode != w) {
            if (!lnode_data.first_header) {
              lnode_data.first_header = w;
              if (loop_data[lnode].nodes.size() > 1)
                w_loop_data.child_loops.push_back(lnode);
            }
          }
        }
      }
      if (valid_loop && w_loop_data.nodes.size() > 1)
        loop_header_ids.push_back(w);
    }
    if (!w_num)
      break;
  }

  // Set back-edge flag correctly for edges through DFS with isAncestor
  visited.clear();
  visited.resize(node_data.size());
  work_list.push(ROOT_ID);

  while(!work_list.empty()) {
    auto cur = work_list.top();
    work_list.pop();

    if (!visited[cur]) {
      visited[cur] = true;
      for (auto &[dst, val, back_edge, def] : node_data[cur].succs) {
        (void)val;
        (void)def;
        work_list.push(dst);
        back_edge = isAncestor(number[dst], number[cur]);
        if (back_edge) {
          for (auto &pred : node_data[dst].preds)
            if (get<0>(pred) == cur)
              get<2>(pred) = true;
        }
      }
    }
  }

  // build child loops relationship for the root node
  auto &root_loop_data = loop_data[ROOT_ID];
  for (auto loop_hdr : loop_header_ids) {
    if (node_data[loop_hdr].header == ROOT_ID)
      root_loop_data.child_loops.push_back(loop_hdr);
  }
}

void LoopTree::printDot(std::ostream &os) const {
  os << "digraph {\n";

  vector<string> lheader_names {
    "none", "nonheader", "self", "reducible", "irreducible"
  };

  // print loop sets
  for (auto &n : loop_header_ids) {
    auto &n_loop_data = loop_data[n];
    auto bb = n;

    cout << bb_dot_name(node_data[bb].bb->getName()) << " -> (";
    for (auto el : n_loop_data.nodes) {
      cout << bb_dot_name(node_data[el].bb->getName());
      if (el != loop_data[n].nodes.back())
        cout << ",";
    }
    cout << ")" << '\n';
  }

  for (auto n : nodes) {
    auto &node = node_data[n];
    auto header_id = node.first_header ? *node.first_header : node.header;
    auto header_bb = node_data[header_id].bb;

    if (header_bb == &f.getFirstBB() && node.bb == header_bb)
      continue;
    auto shape = header_bb == &f.getFirstBB() ? "box" : "oval";
    os << '"' << bb_dot_name(header_bb->getName()) << "\"[label=<"
       << bb_dot_name(header_bb->getName())
       << "<BR /><FONT POINT"
       << "-SIZE=\"10\">" << lheader_names[node_data[header_id].type]
       << "</FONT>>][shape="<< shape <<"];\n";
    os << '"' << bb_dot_name(header_bb->getName()) << "\" -> \""
       << bb_dot_name(node.bb->getName()) << "\";\n";
    os << '"' << bb_dot_name(node.bb->getName()) << "\"[label=<"
       << bb_dot_name(node.bb->getName())
       << "<BR /><FONT POINT-SIZE=\"10\">" << lheader_names[node.type]
       << "</FONT>>]"<<";\n";
  }

  os << "}\n";
}

// Relies on Alive's top_sort run during llvm2alive conversion in order to
// traverse the cfg in reverse postorder to build dominators.
void DomTree::buildDominators() {
  // initialization
  unsigned i = f.getBBs().size();
  for (auto &b : f.getBBs()) {
    if (!b->empty())
      doms.emplace(b, *b).first->second.order = --i;
  }

  // build predecessors relationship
  for (auto [src, tgt, instr] : cfg) {
    (void)instr;
    if (!tgt.empty())
      doms.at(&tgt).preds.push_back(&doms.at(&src));
  }

  auto &entry = doms.at(&f.getFirstBB());
  entry.dominator = &entry;

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
  while (f1->order != f2->order) {
    while (f1->order < f2->order)
      f1 = f1->dominator;
    while (f2->order < f1->order)
      f2 = f2->dominator;
  }
  return f1;
}

// get immediate dominator BasicBlock
const BasicBlock* DomTree::getIDominator(const BasicBlock &bb) const {
  auto dom = doms.at(&bb).dominator;
  return dom ? &dom->bb : nullptr;
}

bool DomTree::dominates(const BasicBlock &bb1, const BasicBlock &bb2) {
  if (&bb1 == &bb2)
    return true;

  DomTreeNode *node = &doms.at(&bb2);
  do {
    node = node->dominator;
    if (&node->bb == &bb1)
      return true;
  } while (&node->bb != &f.getFirstBB());

  return false;
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

