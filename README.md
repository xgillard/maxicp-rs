# MaxiCP-rs

This project aims at implementing a fast, and clean constraint programming
solver with a focus on correctness, simplicity, maintainability and
performance. It is largely inspired by both minicp (https://www.minicp.org) and
maxicp (https://pschaus.github.io/maxicp/).

> **NOTE**: 
> This is pretty much a pet project and a work in progress. 
> We'll see where this leads.

<p align="center">
	<img src="./resources/maxicp-rs_small.png" alt="maxicp-rs-logo" />
</p>

## Roadmap to minimum viable product
* [X] State
    * [X] Implement a trailing mechanism (maybe simpify to only keep one type of signed / unsigned)
    * [X] Implement reversible sparse set
    * [X] Implement reversible interval
* [ ] Engine
    * [X] Implement bool var 
    * [X] Implement int variables
	* [ ] Implement sequence variables
	* [X] Define constraint and propagator traits
	* [ ] Implement the basic constraints
    * [ ] Implement the solver with propagation fixpoint
* [ ] Search
    * [ ] Implement search strategies
* [ ] Bindings
	* [ ] For C++ (with cxx)
	* [ ] For Python3 (with pyo3)
	* [ ] For Java (maybe consider)



## Maybe later
* [ ] State
    * [ ] Implement reversible lazy sparse set (interval that might become a sparse set)
    * [ ] Implement fast and efficient bitsets
    * [ ] Implement reversible bitset
	* [ ] Implement reversible tri partition 
	* [ ] Implement reversible stack (push only)