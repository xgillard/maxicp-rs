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
  * [ ] Implement the solver with propagation fixpoint
  * [ ] Implement the basic constraints
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
