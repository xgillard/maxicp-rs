//
// maxicp-rs is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License  v3
// as published by the Free Software Foundation.
//
// mini-cp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY.
// See the GNU Lesser General Public License  for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with mini-cp. If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
//
// Copyright (c)  2022 by X. Gillard
//

//! This module provides the implementation of an incremental maximum matching
//! algorithm which is useful when implementing the domain consistent propagator
//! for the all different constraint.
//!
//! The details of the algorithm used to implement the DC filtering implemented
//! by the `VarValueGraph` propagator are given in "A filtering algorithm for
//! constraints of difference in CSPs" J-C. Régin, AAAI-94.
//!
//! Essentially, the algorithm operates in two phases:
//!
//! 1. A quick feasibility check is performed. That one states that for a
//!    solution to exist for all different, one must be able to find a maximum
//!    matching between variables and their domain values in the var value
//!    bi-partite graph. In the event where no maximum matching exists that
//!    covers all variables, the all different constraint simply cant be satisfied.
//!
//! 2. When it is known that the constraint is satisfiable, a filtering check
//!    is carried out which can prune away the values having no support from
//!    variable domains. That filtering uses Berge's theorem which states that
//!    an edge belongs to **some** but not all maximum matching iff, for an
//!    arbitrary matching M, it belongs to either an even length alternating
//!    path that starts at an  M-free vertex (case 1), or an even length
//!    alternating cycle (case 2).
//!    In 1994, Regin proposed to treat both cases efficiently trough a simple
//!    graph transformation where:
//!      
//!       - Variables have an inbound edge from their matched value in M and an
//!         outbound edge towards the other.
//!       
//!       - Value nodes have an inbound edge from the sink if they belong to M
//!         and an outbound edhe towards the sink if they dont.
//!       
//!    Thanks to this transformation, both case reduce to the following statement.
//!    An edge belongs to some maximum matching iff it either belongs to the
//!    maximum matching M (obviously !), or it belongs to a cycle in the graph.
//!    In our implementation, all cycles are found using Kosaraju's algorithm to
//!    finding all SCCs.
use std::cell::UnsafeCell;

use crate::prelude::*;

/// This "timestamp" implements a sort of 'monotonic clock' (a counter that
/// can only ever be incremented).
///
/// # Note
///
/// The original maxicp implementation (and minicp FWIW) refer to this timestamp
/// as "magic". I have changed that name because I believe that he timestamp
/// notion better encompasses the idea of a monotonic increasing counted that
/// serves as a passive lock version token.
#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct Timestamp(usize);

impl Timestamp {
    /// Creates a new initial timestamp
    fn new() -> Self {
        Self(0)
    }
    /// Increments the value of the current timestamp
    fn inc(self) -> Self {
        Self(self.0 + 1)
    }
}

/// This is the identifier of a fat variable (position in a vector). This is
/// essentially useful to decouple a the variables (position in the max matching
/// bipartite graph) and the variable itself.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct VarNodeId(usize);

/// This structure represents a cp variable along with the additional metadata
/// it uses when computing a maximum matching
#[derive(Debug)]
struct VarNode {
    /// The identifier of the variable
    id: VarNodeId,
    /// The variable this fat var refers to
    var: Variable,
    /// What time was a value associated with this variable for the last time ?
    seen: Timestamp,
    /// If there is a match associated with this variable, what is it ?
    /// (we'll work with value id rather than the value itself)
    value: Option<ValNodeId>,
    // --- SCC RELATED STUFFS -------------------------------------------------
    /// Inbound nodes
    inbound: Vec<NodeId>,
    /// Outbound nodes
    outbound: Vec<NodeId>,
    status: VisitStatus,
}

/// This is the identifier of a fat value (position in a vector). This is
/// essentially useful to decouple a the value identifier (position in the max
/// matching bipartite graph) and the value itself.
///
/// The varnode ids are zero indexed, however, the values do not necessarily
/// start at zero. There is however a direct mapping between the valnodeid
/// and the value: `value + owner.min == valnodeid` (this might change in the
/// future...it is unlikely though)
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct ValNodeId(usize);

/// This structure represents a cp variable along with the additional metadata
/// it uses when computing a maximum matching
#[derive(Debug)]
struct ValNode {
    /// the value identifier
    id: ValNodeId,
    /// The actual value that is being matched.
    value: isize,
    /// What time was a var associated with this variable for the last time ?
    seen: Timestamp,
    /// If there is a match associated with this variable, what is it ?
    /// (we'll work with value id rather than the value itself)
    variable: Option<VarNodeId>,
    // --- SCC RELATED STUFFS -------------------------------------------------
    /// Inbound nodes
    inbound: Vec<NodeId>,
    /// Outbound nodes
    outbound: Vec<NodeId>,
    status: VisitStatus,
}

/// The sink is only used in the transformed graph in which we used kosaraju's
/// algorithm to finding all SCCs.
#[derive(Debug)]
struct Sink {
    /// Inbound nodes
    inbound: Vec<NodeId>,
    /// Outbound nodes
    outbound: Vec<NodeId>,
    /// The visit status of the sink
    status: VisitStatus,
}
impl Sink {
    /// Creates a new sink
    fn new() -> Self {
        Self {
            inbound: vec![],
            outbound: vec![],
            status: VisitStatus::NotVisited,
        }
    }
}

/// This structure represents the matching (assoc. of a variable w/ a value).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Matching {
    /// The variable associated with 'value' in the computed matching in
    /// the computed matching..
    pub variable: Variable,
    /// The value associated with 'variable' in the computed matching in
    /// the computed matching..
    pub value: isize,
}

/// The details of the algorithm used to implement the DC filtering implemented
/// by the `VarValueGraph` propagator are given in "A filtering algorithm for
/// constraints of difference in CSPs" J-C. Régin, AAAI-94.
///
/// Essentially, the algorithm operates in two phases:
///
/// 1. A quick feasibility check is performed. That one states that for a
///    solution to exist for all different, one must be able to find a maximum
///    matching between variables and their domain values in the var value
///    bi-partite graph. In the event where no maximum matching exists that
///    covers all variables, the all different constraint simply cant be satisfied.
///
/// 2. When it is known that the constraint is satisfiable, a filtering check
///    is carried out which can prune away the values having no support from
///    variable domains. That filtering uses Berge's theorem which states that
///    an edge belongs to **some** but not all maximum matching iff, for an
///    arbitrary matching M, it belongs to either an even length alternating
///    path that starts at an  M-free vertex (case 1), or an even length
///    alternating cycle (case 2).
///    In 1994, Regin proposed to treat both cases efficiently trough a simple
///    graph transformation where:
///      
///       - Variables have an inbound edge from their matched value in M and an
///         outbound edge towards the other.
///       
///       - Value nodes have an inbound edge from the sink if they belong to M
///         and an outbound edhe towards the sink if they dont.
///       
///    Thanks to this transformation, both case reduce to the following statement.
///    An edge belongs to some maximum matching iff it either belongs to the
///    maximum matching M (obviously !), or it belongs to a cycle in the graph.
///    In our implementation, all cycles are found using Kosaraju's algorithm to
///    finding all SCCs.
///
/// This structure is used to compute (repeatedly, and incrementally) a maximum
/// matching in the bipartite node-value graph as is required per the Regin
/// algorithm. The algorithm in itself proceeds by a double dfs to identify
/// the alternating and augmenting path of this bipartite graph.
///
/// The structure also contains whatever it takes to transform the graph and
/// find all SSCs in it as a means to compute an efficient domain consistent
/// filter for the all different constraint.
pub struct VarValueGraph {
    /// The 'timestamp' of the max. matching. This is a kind of passive lock
    /// token which is used to detect if an information has become stale or not
    /// (same mechanism as in the version control of reversible ints).
    timestamp: Timestamp,
    /// These are the variable nodes of the bipartite graph.
    variables: Vec<VarNode>,
    /// These are the value nodes of the bipartite graph.
    values: Vec<ValNode>,
    /// The value of the lowest value in the domain of any variable in the
    /// bipartite graph
    min: isize,
    /// The size of the current matching that has been computed
    size_matching: usize,
    /// The actual matching between variables and values
    _matching: Vec<Matching>,
    // --- SCC RELATED STUFFS -------------------------------------------------
    /// Sink (dummy node of the transformed graph)
    _sink: Sink,
    /// The dfs stack which is used when computing the scc in this var value
    /// graph (this field is not stricly required, but is avoids to repeatedly
    /// allocate the same vector)
    _stack: UnsafeCell<Vec<NodeId>>,
    /// The suffix order stack which is used when computing the scc in this var
    /// value graph (this field is not stricly required, but is avoids to
    /// repeatedly allocate the same vector)
    _suffix_order: Vec<NodeId>,
}

impl VarValueGraph {
    /// This creates a variable-values bipartite graph that can be used to
    /// compute a maximum matching that can be used in the context of the
    /// filtering of an all different constraint.
    pub fn new(cp: &CpModel, xs: &[Variable]) -> Self {
        let timestamp = Timestamp::new();

        let mut min = isize::MAX;
        let mut max = isize::MIN;

        let mut variables = vec![];
        for (i, var) in xs.iter().copied().enumerate() {
            min = min.min(cp.min(var).unwrap_or(isize::MAX));
            max = max.max(cp.max(var).unwrap_or(isize::MIN));
            variables.push(VarNode {
                id: VarNodeId(i),
                var,
                seen: timestamp,
                value: None,
                //
                inbound: vec![],
                outbound: vec![],
                status: VisitStatus::NotVisited,
            });
        }

        let mut values = vec![];
        for (id, value) in (min..=max).enumerate() {
            values.push(ValNode {
                id: ValNodeId(id),
                value,
                seen: timestamp,
                variable: None,
                //
                inbound: vec![],
                outbound: vec![],
                status: VisitStatus::NotVisited,
            });
        }

        let mut me = Self {
            timestamp,
            variables,
            values,
            //
            min,
            size_matching: 0,
            //
            _matching: vec![],
            //
            _sink: Sink::new(),
            _stack: UnsafeCell::new(vec![]),
            _suffix_order: vec![],
        };

        me.find_initial_matching(cp);
        me
    }
}

impl Propagator for VarValueGraph {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        let matching = self.compute_maximum_matching(cp);
        if matching.len() < self.variables.len() {
            Err(Inconsistency)
        } else {
            self.prepare_transformed_graph(cp);
            self.kosaraju_scc();

            for var_node in self.variables.iter() {
                let vmin = cp.min(var_node.var).unwrap();
                let vmax = cp.max(var_node.var).unwrap();
                let skip = (vmin - self.min) as usize;
                let take = (vmax - vmin) as usize;

                for val_node in self.values.iter().skip(skip).take(take) {
                    if var_node.value != Some(val_node.id) && var_node.status != val_node.status {
                        cp.remove(var_node.var, val_node.value)?;
                    }
                }
            }
            Ok(())
        }
    }
}

// ********************************************************************** //
// ****** MAXIMUM MATCHING ********************************************** //
// ********************************************************************** //
impl VarValueGraph {
    /// This function computes a maximum matching in the bipartite variable
    /// value graph if the domains of the variables have been updated in a way
    /// that invalidates the previously computed maximum matching. When the
    /// maximum matching computed this way does not cover all variables, then
    /// there is no possible way of satisfying the constraint.
    pub fn compute_maximum_matching(&mut self, cp: &CpModel) -> &[Matching] {
        for var in self.variables.iter_mut() {
            if let Some(val_id) = var.value {
                let value = self.values[val_id.0].value;
                if !cp.contains(var.var, value) {
                    self.values[val_id.0].variable = None;
                    var.value = None;
                    self.size_matching -= 1;
                }
            }
        }

        self.find_maximal_matching(cp);

        self._matching.clear();
        for v in self.variables.iter() {
            if let Some(value) = v.value {
                self._matching.push(Matching {
                    variable: v.var,
                    value: value.0 as isize + self.min,
                });
            }
        }
        &self._matching
    }
    /// This function computes a greedy initial matching between variables and
    /// values. This matching is the one that will be re optimized when a new
    /// maximum matching is required.
    fn find_initial_matching(&mut self, cp: &CpModel) {
        self.size_matching = 0;
        for varnode in self.variables.iter_mut() {
            let vmin = cp.min(varnode.var).unwrap();
            let vmax = cp.max(varnode.var).unwrap();

            for value in vmin..=vmax {
                let valnode = &mut self.values[(value - self.min) as usize];
                if valnode.variable.is_none() && cp.contains(varnode.var, valnode.value) {
                    varnode.value = Some(valnode.id);
                    valnode.variable = Some(varnode.id);
                    self.size_matching += 1;
                    break;
                }
            }
        }
    }
    /// This method computes a maximum matching in the bipartite variable
    /// values graphs by extending and adapting an existing matching with
    /// alternating (augmenting) paths.
    fn find_maximal_matching(&mut self, cp: &CpModel) {
        let n = self.variables.len();
        if self.size_matching < n {
            for k in 0..n {
                let x = &self.variables[k];
                let xval = x.value;
                let xid = x.id;
                if xval.is_none() {
                    self.timestamp = self.timestamp.inc();
                    if self.find_alternating_path_from_var(cp, xid) {
                        self.size_matching += 1;
                    }
                }
            }
        }
    }
    /// Returns true iff a new alternating path can be found starting from
    /// the given variable node.
    fn find_alternating_path_from_var(&mut self, cp: &CpModel, var_id: VarNodeId) -> bool {
        let varnode = &self.variables[var_id.0];
        let varseen = varnode.seen;
        let varvar = varnode.var;
        let varval = varnode.value;
        if varseen != self.timestamp {
            self.variables[var_id.0].seen = self.timestamp;

            let xmin = cp.min(varvar).unwrap();
            let xmax = cp.max(varvar).unwrap();

            for value in xmin..=xmax {
                let val_id = ValNodeId((value - self.min) as usize);
                if varval != Some(val_id)
                    && cp.contains(varvar, value)
                    && self.find_alternating_path_from_val(cp, val_id)
                {
                    self.variables[var_id.0].value = Some(val_id);
                    self.values[val_id.0].variable = Some(var_id);
                    return true;
                }
            }
        }
        false
    }
    /// Returns true iff a new alternating path can be found starting from
    /// the given value node.
    fn find_alternating_path_from_val(&mut self, cp: &CpModel, val_id: ValNodeId) -> bool {
        let valnode = &mut self.values[val_id.0];
        if valnode.seen != self.timestamp {
            valnode.seen = self.timestamp;

            if valnode.variable.is_none() {
                return true;
            }
            if let Some(var_id) = valnode.variable {
                return self.find_alternating_path_from_var(cp, var_id);
            }
        }
        false
    }
}

// ********************************************************************** //
// ****** SCC *********************************************************** //
// ********************************************************************** //

/// Kosaraju's algorithm identifies all SCC in a graph by performing a double
/// DFS search in the graph. This status acts as a marker to tell whether a
/// node is open to being visited, if its successors have already been pushed
/// down the stack or if the complete subtree behind it has been visited.
///
/// # Note:
/// When a node is closed, the node id inside of the closed status corresponds
/// to the root of the dfs exploration which led to that node's closure. In
/// the context of SCC, this node identifier acts as an SCC identity.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum VisitStatus {
    /// The status of a node whose sucessors have not been pushed down the
    /// stack. Whenever a node wih this status is encountered during DFS, it
    /// must be visited (expanded = successors pushed on the stack).
    NotVisited,
    /// A node whose visitor have already been pushed on the stack for
    /// exploration. When such a node is encountered during exploration,
    /// there is no need to push it on the stack again.
    Visited,
    /// The status of a node whose complete subtree has been explored.
    /// node-id is the root of the dfs exploration that closed this node
    Closed(NodeId),
}

/// Polymorphic node identifier.
///
/// The VarValueGraph uses three distinct types of nodes when computing the
/// maximum matching (which is simpler). However, these nodes along with the
/// sink have to be considered indistinct when computing the SCC of the
/// transformed graph. This polymorphic nodeid makes for an easy manipulation of
/// these different kind of nodes in an uniform way.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum NodeId {
    /// Uniquely identifies a variable node
    VarNode(VarNodeId),
    /// Uniquely identifies a value node
    ValNode(ValNodeId),
    /// Uniquely identifies the sink of the transformed graph.
    Sink,
}

impl VarValueGraph {
    /// prepares the transformed var value graph where there is:
    ///
    /// * one outgoing arc from each variable node to each value node in its
    ///   domain ++except for the value to which the variable is matched++
    ///
    /// * one inbound arc to each varible node from its matched value
    ///
    /// * the values not participating in the maximum matching have an outgoing
    ///   arc towards the sink
    ///
    /// * the values participating in the maximum matching have an incoming arc
    ///   from the graph sink
    fn prepare_transformed_graph(&mut self, cp: &CpModel) {
        self.clear_adjacency_lists();

        // builds the connections between the variable and value nodes
        for var in self.variables.iter_mut() {
            for value in cp.iter(var.var) {
                let val_pos = (value - self.min) as usize;
                let val_id = ValNodeId(val_pos);

                if Some(val_id) == var.value {
                    var.inbound.push(NodeId::ValNode(val_id));
                    self.values[val_pos].outbound.push(NodeId::VarNode(var.id));
                } else {
                    var.outbound.push(NodeId::ValNode(val_id));
                    self.values[val_pos].inbound.push(NodeId::VarNode(var.id));
                }
            }
        }

        // builds the connections between the value nodes and the sink
        for val in self.values.iter_mut() {
            // it belongs to the maximum matching
            if val.variable.is_some() {
                val.inbound.push(NodeId::Sink);
                self._sink.outbound.push(NodeId::ValNode(val.id));
            } else {
                val.outbound.push(NodeId::Sink);
                self._sink.inbound.push(NodeId::ValNode(val.id));
            }
        }
    }

    /// This function executes kosaraju's algorithm to find
    /// components in the transformed variable value graph.
    fn kosaraju_scc(&mut self) {
        let nb_var = self.variables.len();
        let nb_val = self.values.len();

        // clear visit statuses
        self.clear_visit_status();
        // perform a dfs1 traversal of all nodes
        for var in 0..nb_var {
            self.dfs1(NodeId::VarNode(VarNodeId(var)));
        }
        for val in 0..nb_val {
            self.dfs1(NodeId::ValNode(ValNodeId(val)));
        }
        self.dfs1(NodeId::Sink);

        // clear visit statuses
        self.clear_visit_status();

        // the suffix order is now ready, we can peform a dfs2 traversal
        // (in the transposed graph) in the reverse suffix order to identify
        // all SCCs
        while let Some(id) = self._suffix_order.pop() {
            self.dfs2(id);
        }
    }

    /// clears the visit status of all nodes in the var value graph
    fn clear_visit_status(&mut self) {
        self.variables
            .iter_mut()
            .for_each(|v| v.status = VisitStatus::NotVisited);
        self.values
            .iter_mut()
            .for_each(|v| v.status = VisitStatus::NotVisited);
        self._sink.status = VisitStatus::NotVisited;
    }
    /// clears the adjacency lists of all nodes int the var value graph
    fn clear_adjacency_lists(&mut self) {
        self.variables.iter_mut().for_each(|v| {
            v.inbound.clear();
            v.outbound.clear();
        });
        self.values.iter_mut().for_each(|v| {
            v.inbound.clear();
            v.outbound.clear();
        });
        self._sink.inbound.clear();
        self._sink.outbound.clear();
    }
    /// Lists the neighbors of the node identified by `id` which are connected
    /// to `id` with an arc directed towards `id`
    fn inbound(&self, id: NodeId) -> &[NodeId] {
        match id {
            NodeId::VarNode(id) => &self.variables[id.0].inbound,
            NodeId::ValNode(id) => &self.values[id.0].inbound,
            NodeId::Sink => &self._sink.inbound,
        }
    }
    /// Lists the neighbors of the node identified by `id` which are connected
    /// to `id` with an arc leaving `id` towards these other nodes
    fn outbound(&self, id: NodeId) -> &[NodeId] {
        match id {
            NodeId::VarNode(id) => &self.variables[id.0].outbound,
            NodeId::ValNode(id) => &self.values[id.0].outbound,
            NodeId::Sink => &self._sink.outbound,
        }
    }
    /// Returns the visit status of the node identified with `id`
    fn get_status(&self, id: NodeId) -> VisitStatus {
        match id {
            NodeId::VarNode(id) => self.variables[id.0].status,
            NodeId::ValNode(id) => self.values[id.0].status,
            NodeId::Sink => self._sink.status,
        }
    }
    /// Updates the visit status of the node identified with `id` and assigns it
    /// the value `status`
    fn set_status(&mut self, id: NodeId, status: VisitStatus) {
        match id {
            NodeId::VarNode(id) => self.variables[id.0].status = status,
            NodeId::ValNode(id) => self.values[id.0].status = status,
            NodeId::Sink => self._sink.status = status,
        }
    }
    /// This method performs the 1st dfs traversal of the graph from the
    /// kosaraju's SCC algo. It traverses the graph itself and populates the
    /// `suffix_order` field which is used for the rest of the SCC computation.
    fn dfs1(&mut self, root_id: NodeId) {
        if self.get_status(root_id) == VisitStatus::NotVisited {
            self._stack.get_mut().push(root_id);
        }

        while !self._stack.get_mut().is_empty() {
            let current = self._stack.get_mut().pop().unwrap();
            let status = self.get_status(current);
            match status {
                VisitStatus::NotVisited => {
                    self._stack.get_mut().push(current); // leave it on the stack for now
                    self.set_status(current, VisitStatus::Visited);
                    for adj in self.outbound(current) {
                        let adj = *adj;
                        if self.get_status(adj) == VisitStatus::NotVisited {
                            // SAFETY:
                            // This is okay, the other self borrow actually only
                            // ever borrow one node. The stack is not impacted
                            // by these borrows.
                            unsafe { (*self._stack.get()).push(adj) };
                        }
                    }
                }
                VisitStatus::Visited => {
                    self._suffix_order.push(current);
                    self.set_status(current, VisitStatus::Closed(root_id));
                }
                VisitStatus::Closed(_) => { /* do nothing, that's ok */ }
            }
        }
    }
    /// This method performs the 2st dfs traversal of the graph from the
    /// kosaraju's SCC algo. It traverses the transposed graph (which differs
    /// from `dfs1()`)
    fn dfs2(&mut self, root_id: NodeId) {
        if self.get_status(root_id) == VisitStatus::NotVisited {
            self._stack.get_mut().push(root_id);
        }
        while !self._stack.get_mut().is_empty() {
            let current = self._stack.get_mut().pop().unwrap();
            let status = self.get_status(current);
            match status {
                VisitStatus::NotVisited => {
                    self._stack.get_mut().push(current); // leave it on the stack for now
                    self.set_status(current, VisitStatus::Visited);
                    for adj in self.inbound(current) {
                        let adj = *adj;
                        if self.get_status(adj) == VisitStatus::NotVisited {
                            // SAFETY:
                            // This is okay, the other self borrow actually only
                            // ever borrow one node. The stack is not impacted
                            // by these borrows.
                            unsafe { (*self._stack.get()).push(adj) };
                        }
                    }
                }
                VisitStatus::Visited => {
                    self.set_status(current, VisitStatus::Closed(root_id));
                }
                VisitStatus::Closed(_) => { /* do nothing, that's ok */ }
            }
        }
    }
}

#[cfg(test)]
mod test_maxmatching {
    use crate::prelude::*;

    use super::{Matching, VarValueGraph};

    #[test]
    fn test1() {
        let mut cp = CpModel::default();
        let vars = vec![
            ivar(&mut cp, &[1, 2]),
            ivar(&mut cp, &[1, 2]),
            ivar(&mut cp, &[1, 2, 3, 4]),
        ];
        let mut maxmatch = VarValueGraph::new(&cp, &vars);
        let mut matching = maxmatch.compute_maximum_matching(&cp);

        check(&cp, matching, 3);
        cp.remove(vars[2], 3).ok();
        cp.fixpoint().ok();

        matching = maxmatch.compute_maximum_matching(&cp);
        check(&cp, matching, 3);

        cp.remove(vars[2], 4).ok();
        cp.fixpoint().ok();
        matching = maxmatch.compute_maximum_matching(&cp);
        check(&cp, matching, 2);
    }

    #[test]
    fn test2() {
        let mut cp = CpModel::default();
        let vars = vec![
            ivar(&mut cp, &[1, 4, 5]),
            ivar(&mut cp, &[9, 10]),         // will be 10
            ivar(&mut cp, &[1, 4, 5, 8, 9]), // will be 8 or 9
            ivar(&mut cp, &[1, 4, 5]),
            ivar(&mut cp, &[1, 4, 5, 8, 9]),
            ivar(&mut cp, &[1, 4, 5]),
        ];
        let mut maxmatch = VarValueGraph::new(&cp, &vars);
        let mut matching = maxmatch.compute_maximum_matching(&cp);

        check(&cp, matching, 6);
        cp.remove(vars[5], 5).ok();
        cp.fixpoint().ok();

        matching = maxmatch.compute_maximum_matching(&cp);
        check(&cp, matching, 6);

        cp.remove(vars[0], 5).ok();
        cp.remove(vars[3], 5).ok();
        cp.fixpoint().ok();
        matching = maxmatch.compute_maximum_matching(&cp);
        check(&cp, matching, 5);
    }

    fn ivar(cp: &mut CpModel, val: &[isize]) -> Variable {
        let min = val.first().copied().unwrap();
        let max = val.last().copied().unwrap();
        let var = cp.new_int_var(min, max);

        let mut v = val.iter().copied();
        let mut k = v.next();
        for i in min..=max {
            if Some(i) == k {
                k = v.next();
            } else {
                cp.remove(var, i).ok();
            }
        }
        var
    }

    fn check(cp: &CpModel, matching: &[Matching], expected_sz: usize) {
        assert_eq!(expected_sz, matching.len());
        for m in matching {
            assert!(cp.contains(m.variable, m.value));
        }
    }
}
