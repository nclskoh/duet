/********************************************************************************
    Author: Charlie Murphy
    Email:  tcm3@cs.princeton.edu

    Date:   May 19, 2017

    Description: Header file for various types used in embedding algorithm.
    Provides a class interface for combining the universe and predicate graphs
 ********************************************************************************/

#include <vector>
#include <map>
#include <queue>
#include <cstdint>
#include "graph.h"

#ifndef CM_EMBEDDING_H
#define CM_EMBEDDING_H

/* The label for the proposition graph predicate symbol and list of arguments */
struct prop{
  prop (size_t p = 0) : pred(p) {}
  /* copy semantics / cast to const if you want to copy a non-const vector*/
  prop (size_t p, const std::vector<int>& v) : pred(p), vars(v) {}
  /* move semantics (default) */
  prop (size_t p, std::vector<int>& v) : pred(p), vars(std::move(v)) {}
  size_t pred;
  std::vector<int> vars;
};

/* The type of decisions:
     u: vertex in predicate graph
     pos: choice of edge eminating from u
     u_edges : edges of universe graph removed due to decision */
struct decision{
  decision(size_t pu = 0, size_t ppos = 0) : u(pu), pos(ppos) {}
  /* copy semantics */
  decision(size_t pu, size_t ppos, const std::vector<Graph::VertexPair>& ue,
	  const std::vector<Graph::VertexPair>& pe,
	  const std::vector<Graph::Edge>& adj) : u(pu), pos(ppos), u_edges(ue), p_edges(pe), pu_adj(adj) {}
  /* move semantics (default) */
  decision(size_t pu, size_t ppos, std::vector<Graph::VertexPair>& ue,
	  std::vector<Graph::VertexPair>& pe,
	  const std::vector<Graph::Edge>& adj) : u(pu), pos(ppos), u_edges(std::move(ue)), p_edges(std::move(pe)), pu_adj(adj) {}
  size_t u;
  size_t pos;
  std::vector<Graph::VertexPair> u_edges;
  std::vector<Graph::VertexPair> p_edges;
  std::vector<Graph::Edge> pu_adj;
};

struct udecision{
    size_t u;
    size_t v;
    std::vector<Graph::VertexPair> remove_u;
    std::vector<Graph::VertexPair> remove_p;
    udecision(size_t _u, size_t _v) : u(_u), v(_v) { }
    udecision(size_t _u, size_t _v, std::vector<Graph::VertexPair>& _remove_u, std::vector<Graph::VertexPair>& _remove_p) : u(_u), v(_v), remove_u(_remove_u), remove_p(_remove_u) { }
};

/* Assume sig1 and sig2 represent multisets of elements */
bool subset(const std::vector<uint8_t>& sig1, const std::vector<uint8_t>& sig2){
  bool subset(sig1.size() <= sig2.size());
  for (size_t i = 0; subset && i < sig1.size(); ++i){ /* assert(sig1.size() <= sig2.size()) */
    subset = sig1[i] <= sig2[i];
  }
  return subset;
}

class Embedding{
  Graph u_graph_;
  LabeledGraph<prop, prop> p_graph_;
  /* (vert, pos) \in u_inv_label_[u] -> p_graph_.getULabel(vert).vars[pos] = u */
  std::vector<std::vector<Graph::Edge>> u_inv_label_;
  /* (vert, pos) \in u_inv_label_[v] -> p_graph_.getVLabel(vert).vars[pos] = v */
  std::vector<std::vector<Graph::Edge>> v_inv_label_;
  bool valid_;

  /* finish constructing the universe graph */
  void fill_ugraph(const std::vector<std::vector<uint8_t>>& sigs1, const std::vector<std::vector<uint8_t>>& sigs2){
    std::vector<std::vector<size_t>> adj;
    adj.resize(sigs1.size());

    /* use adj as placeholder in order to safely parallel ize */
    #pragma omp parallel for schedule(guided)
    for (size_t i = 1; i < sigs1.size(); ++i){
      for (size_t j = 1; j < sigs2.size(); ++j){
        if (subset(sigs1[i], sigs2[j])){
	  adj[i].push_back(j);
	}
      }
    }
    /* Add (undirected) edges to universe graph */
    for (size_t i = 1; i < adj.size(); ++i){
      for (size_t j = 0; j < adj[i].size(); ++j){
	u_graph_.add_edge(i, adj[i][j]);
      }
    }

    /* It doesn't matter what is removed */
    std::vector<Graph::VertexPair> tmp;
    std::vector<int> junk;
    valid_ = u_graph_.unit_prop(tmp, junk, junk);
  }

  /* finish constructing the predicate graph */
  void fill_pgraph(){
    for (size_t i = 0; i < p_graph_.uSize(); ++i){
      const prop& u_label = p_graph_.getULabel(i);
      for (size_t j = 0; j < p_graph_.vSize(); ++j){
	const prop& v_label = p_graph_.getVLabel(j);
	if (u_label.pred == v_label.pred){
	  bool mem(true);
	  for (size_t k = 0; mem && k < u_label.vars.size(); ++k){
	    mem = u_graph_.has_edge(u_label.vars[k], v_label.vars[k]);
	  }
	  if (mem) p_graph_.add_edge(i, j);
	}
      }
    }
    for (size_t i = 0; i < p_graph_.uSize(); ++i){
      if (p_graph_.uAdj(i).size() == 1){
	std::vector<Graph::VertexPair> junk;
        choose_constraint(i, p_graph_.uAdj(i)[0].vertex, junk, junk);
	break;
      } else if (p_graph_.uAdj(i).size() == 0){
	valid_ = false;
	break;
      }
    }
  }

  /* construct inverse label */
  void fill_inv_label(){
    u_inv_label_.resize(u_graph_.uSize());
    for (size_t i = 0; i < p_graph_.uSize(); ++i){
      const std::vector<int>& vars = p_graph_.getULabel(i).vars;
      for (size_t k = 0; k < vars.size(); ++k){
	u_inv_label_[vars[k]].emplace_back(i, k);
      }
    }

    v_inv_label_.resize(u_graph_.vSize());
    for (size_t i = 0; i < p_graph_.vSize(); ++i){
      const std::vector<int>& vars = p_graph_.getVLabel(i).vars;
      for (size_t k = 0; k < vars.size(); ++k){
	v_inv_label_[vars[k]].emplace_back(i, k);
      }
    }
  }
  
 public:
  Embedding() : valid_(true) {}

  /* Copy Semantics */
  Embedding(const std::vector<std::vector<uint8_t>>& sigs1, const std::vector<std::vector<uint8_t>>& sigs2,
	    const std::vector<prop>& pu_label, const std::vector<prop>& pv_label) : u_graph_(sigs1.size(), sigs2.size()), valid_(true) {
    fill_ugraph(sigs1, sigs2);
    p_graph_ = std::move(LabeledGraph<prop, prop>(pu_label, pv_label));
    fill_pgraph();
    fill_inv_label();
  }

  /* Move Semantics */
  Embedding(const std::vector<std::vector<uint8_t>>& sigs1, const std::vector<std::vector<uint8_t>>& sigs2,
	    std::vector<prop>& pu_label, std::vector<prop>& pv_label) : u_graph_(sigs1.size(), sigs2.size()), valid_(true) {
    fill_ugraph(sigs1, sigs2);
    p_graph_ = std::move(LabeledGraph<prop, prop>(pu_label, pv_label));
    fill_pgraph();
    fill_inv_label();
  }

  Graph& get_universe_graph() { return u_graph_; }
  const Graph& get_universe_graph() const { return u_graph_; }
  LabeledGraph<prop, prop>& get_predicate_graph() { return p_graph_; }
  const LabeledGraph<prop, prop>& get_predicate_graph() const { return p_graph_; }
  bool get_valid() const { return valid_; }

  /* Assert that the constraint p_graph_.uLabel(pu) |-> p_graph_.vLabel(pv)
     and performs "arc consistency" */
  void choose_constraint(size_t pu, size_t pv, std::vector<Graph::VertexPair>& p_removed,
			 std::vector<Graph::VertexPair>& u_removed){
    std::vector<Graph::VertexPair> tmp;
    tmp = std::move(u_graph_.commit_edges(p_graph_.getULabel(pu).vars, p_graph_.getVLabel(pv).vars));
    u_removed.insert(u_removed.end(), tmp.begin(), tmp.end());
    ufilter(u_removed, p_removed);
  }

  /* Commit to a decision and ensure arc consistency. */
  void decide(udecision& d) {
      std::vector<int> u_units, v_units;
      std::vector<Graph::VertexPair> tmp;

      u_units.push_back(d.u);
      v_units.push_back(d.v);

      tmp = std::move(u_graph_.commit_edges(u_units, v_units));
      d.remove_u.insert(d.remove_u.begin(), tmp.begin(), tmp.end());

      ufilter(d.remove_u, d.remove_p);
  }

  void ufilter(std::vector<Graph::VertexPair>& remove_u, std::vector<Graph::VertexPair>& remove_p) {
      bool filtered = true; // More filtering to do?
      while (valid_ && filtered) {
	  filtered = false;
	  for (size_t p = 0; p < p_graph_.uSize(); ++p){
	      const std::vector<Graph::Edge>& p_adj = p_graph_.uAdj(p);
	      const std::vector<int>& p_vars = p_graph_.getULabel(p).vars;

	      /* For each edge p(x_1,...,x_n) -> q(y_1, ..., y_n) in the
		 predicate graph, ensure that each of x_1 -> y_1, ..., x_n ->
		 y_n is the universe graph. */
	      size_t q = 0;
	      while (q < p_adj.size()) {
		  const std::vector<int>& q_vars = p_graph_.getVLabel(p_adj[q].vertex).vars;
		  bool remove_pq = false;
		  for (size_t i = 0; !remove_pq && i < p_vars.size(); ++i) {
		      const std::vector<Graph::Edge>& u_adj = u_graph_.uAdj(p_vars[i]);
		      size_t v;
		      // check if x_i -> y_i
		      for (v = 0; v < u_adj.size() && u_adj[v].vertex != (size_t)q_vars[i]; v++) ;
		      if (v == u_adj.size()) {
			  remove_pq = true;
		      }
		  }
		  if (remove_pq) {
		      remove_p.emplace_back(p, p_adj[q].vertex);
		      p_graph_.remove_edge(p, q);
		      filtered = true;
		  } else {
		      q++;
		  }
	      }
	      if (p_adj.size() == 0) {
		  valid_ = false;
		  return;
	      }

	      /* Suppose that x_i -> y.  Then there must be some p(x_1,...,x_n) ->
		 q(y_1, ..., y_n) in the predicate graph with y = y_i */
	      for (size_t i = 0; i < p_vars.size(); ++i) {
		  const std::vector<Graph::Edge>& xi_adj = u_graph_.uAdj(p_vars[i]);
		  size_t y = 0;
		  while (y < xi_adj.size()) {
		      bool remove_xiy = true;
		      for (size_t q = 0; remove_xiy && q < p_adj.size(); ++q){
			  const std::vector<int>& q_vars = p_graph_.getVLabel(p_adj[q].vertex).vars;
			  if (xi_adj[y].vertex == (size_t)q_vars[i]) {
			      remove_xiy = false;
			  }
		      }
		      if (remove_xiy) {
			  remove_u.emplace_back(p_vars[i], xi_adj[y].vertex);
			  u_graph_.remove_edge(p_vars[i], y);
			  filtered = true;
		      } else {
			  y++;
		      }
		  }
		  if (xi_adj.size() == 0) {
		      valid_ = false;
		      return;
		  }
	      }
	  }
      }
  }

  void add_back(const std::vector<Graph::VertexPair>& p_edges, const std::vector<Graph::VertexPair>& u_edges){
    valid_ = true;
    for (size_t i = 0; i < p_edges.size(); ++i){
      p_graph_.add_edge(p_edges[i].u, p_edges[i].v);
    }
    for (size_t i = 0; i < u_edges.size(); ++i){
      u_graph_.add_edge(u_edges[i].u, u_edges[i].v);
    }
  }
};

#endif