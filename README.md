# MaxiCP-rs

[![Rust](https://github.com/xgillard/maxicp-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/xgillard/maxicp-rs/actions/workflows/rust.yml)
[![codecov](https://codecov.io/github/xgillard/maxicp-rs/branch/main/graph/badge.svg?token=BAZOQHVLH3)](https://codecov.io/github/xgillard/maxicp-rs)

This project aims at implementing a fast, and clean constraint programming
solver with a focus on correctness, simplicity, maintainability and
performance. It is largely inspired by both minicp (<https://www.minicp.org>)
and maxicp (<https://pschaus.github.io/maxicp/>).

> **NOTE**:
> This is pretty much a pet project and a work in progress.
> We'll see where this leads.

<p align="center">
	<img src="./resources/maxicp-rs_small.png" alt="maxicp-rs-logo" />
</p>

## Roadmap to minimum viable product

* [X] State
  * [X] Implement a trailing mechanism
  * [X] Implement reversible sparse set
  * [X] Implement reversible interval
* [ ] Engine
  * [X] Implement bool var
  * [X] Implement int variables
  * [X] Define constraint and propagator traits
  * [X] Implement the solver with propagation fixpoint
  * [X] Test the solver propagation
  * [X] Implement views
  * [ ] Implement the basic constraints
    * [X] Abs value :: x == |y|
    * [X] not equal const :: x != v
    * [X] not equal :: x != y
    * [X] is not equal :: b <==> (x != v)
    * [X] is not equal (var) :: b <==> (x != y)
    * [X] equal :: x == y
    * [X] is equal :: b <==> x == v
    * [X] is equal (var) :: b <==> x == y
    * [X] LE :: x <= v
    * [X] LE :: x <= y
    * [X] GE :: x >= v
    * [X] GE :: x >= y
    * [X] is LE :: b <==> x <= v
    * [X] is LE (var) :: b <==> x <= y
    * [X] is GE :: b <==> (x >= v)
    * [X] is GE (var) :: b <==> (x >= y)
    * [X] must be true x + must be false
    * [ ] is or (var) :: b <==> (x || y)
    * [ ] maximum
    * [ ] sum
    * [ ] All diff binary
    * [ ] All diff dc
    * [ ] All diff fwc
    * [ ] All diff binary
    * [ ] circuit
    * [ ] cumulative
    * [ ] cumulative decomp
    * [ ] disjunctive
    * [ ] element_1d
    * [ ] element_1d DC
    * [ ] element_2d
* [ ] Search
  * [ ] Implement search strategies
* [ ] Bindings
  * [ ] For Python3 (with pyo3)
  * [ ] For C++ (with cxx)
  * [ ] For Java (maybe consider)

## Maybe later

* [ ] State
  * [ ] Implement reversible lazy sparse set
  * [ ] Implement fast and efficient bitsets
  * [ ] Implement reversible bitset
  * [ ] Implement reversible tri partition
  * [ ] Implement reversible stack (push only)
* [ ] Engine
  * [ ] Implement sequence variables
  * [ ] Implement more constraints (tables)
