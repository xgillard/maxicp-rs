
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
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
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
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
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

/// This structure is used to compute (repeatedly, and incrementally) a maximum
/// matching in the bipartite node-value graph as is required per the Regin
/// algorithm. The algorithm in itself proceeds by a double dfs to identify
/// the alternating and augmenting path of this bipartite graph.
pub struct VarValueBipartiteGraph {
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
}

impl VarValueBipartiteGraph {
    /// This creates a variable-values bipartite graph that can be used to 
    /// compute a maximum matching that can be used in the context of the 
    /// filtering of an all different constraint.
    pub fn new(cp: &CpModel, xs: &[Variable]) -> Self {
        let timestamp = Timestamp::default();

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
            });
        }

        let mut values = vec![];
        for (id, value) in (min..=max).enumerate() {
            values.push(ValNode {
                id: ValNodeId(id),
                value, 
                seen: timestamp,
                variable: None,
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
        };

        me.find_initial_matching(cp);
        me
    }

    /// This function computes a maximum matching in the bipartite variable 
    /// value graph if the domains of the variables have been updated in a way
    /// that invalidates the previously computed maximum matching. When the 
    /// maximum matching computed this way does not cover all variables, then 
    /// there is no possible way of satisfying the constraint.
    pub fn  compute_maximum_matching(&mut self, cp: &CpModel) -> &[Matching] {
        for var in self.variables.iter_mut() {
            if let Some(val_id) = var.value {
                let value = self.values[val_id.0];
                if !cp.contains(var.var, value.value) {
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
                let valnode = &mut self.values[(value-self.min) as usize];
                if valnode.variable.is_none() {
                    if cp.contains(varnode.var, valnode.value) {
                        varnode.value = Some(valnode.id);
                        valnode.variable = Some(varnode.id);
                        self.size_matching += 1;
                        break;
                    }
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
                let x = self.variables[k];
                if x.value.is_none() {
                    self.timestamp = self.timestamp.inc();
                    if self.find_alternating_path_from_var(cp, x.id) {
                        self.size_matching += 1;
                    }
                }
            }
        }
    }
    /// Returns true iff a new alternating path can be found starting from 
    /// the given variable node.
    fn find_alternating_path_from_var(&mut self, cp: &CpModel, var_id: VarNodeId) -> bool {
        let varnode  = self.variables[var_id.0];
        if varnode.seen != self.timestamp {
            self.variables[var_id.0].seen = self.timestamp;
            
            let xmin = cp.min(varnode.var).unwrap();
            let xmax = cp.max(varnode.var).unwrap();

            for value in xmin..=xmax {
                let val_id = ValNodeId((value - self.min) as usize);
                if varnode.value != Some(val_id) {
                    if cp.contains(varnode.var, value) {
                        if self.find_alternating_path_from_val(cp, val_id) {
                            self.variables[var_id.0].value = Some(val_id);
                            self.values[val_id.0].variable = Some(var_id);
                            return true;
                        }
                    } 
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

#[cfg(test)]
mod test_maxmatching {
    use crate::prelude::*;

    use super::{Matching, VarValueBipartiteGraph};

    #[test]
    fn test1() {
        let mut cp = CpModel::default();
        let vars = vec![
            ivar(&mut cp, &[1, 2]),
            ivar(&mut cp, &[1, 2]),
            ivar(&mut cp, &[1, 2, 3, 4]),
        ];
        let mut maxmatch = VarValueBipartiteGraph::new(&cp, &vars);
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
            ivar(&mut cp, &[9, 10]), // will be 10
            ivar(&mut cp, &[1, 4, 5, 8, 9]),// will be 8 or 9
            ivar(&mut cp, &[1, 4, 5]),
            ivar(&mut cp, &[1, 4, 5, 8, 9]),
            ivar(&mut cp, &[1, 4, 5]),
        ];
        let mut maxmatch = VarValueBipartiteGraph::new(&cp, &vars);
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
                cp.remove(var, i);
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
