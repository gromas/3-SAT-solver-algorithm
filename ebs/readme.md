# EBS: Entropic Beam Search for SAT

This directory contains the implementation of **EBS (Entropic Beam Search)** — an algebraic SAT solver that combines beam search with an entropy controller for adaptive resource management.

---

## Overview

EBS is built on top of the PQ-Algorithm's elimination order and implements the ideas discussed in the main [README](../README.md). It views the SAT solving process as navigating a space of partial assignments, where the goal is to find a path (assignment) with zero conflicts.

## Key Components

*   **`ebs.py`**: The main implementation file.
*   **`PQPlanner`**: Uses the PQ-Algorithm to compute an optimal variable elimination order.
*   **`ViterbiCore`**: A beam search engine that maintains `K` best paths (partial assignments). It uses **ANF (Algebraic Normal Form)** polynomials to represent constraints and bitmasks for fast clause satisfaction checks.
*   **`EntropyController`**: Dynamically adjusts the beam size (`beam_size`) and diversity based on the `∑P(t)²` integral (the "volume" of the search space). This implements the **Payload × Quantum** duality from the main paper.
*   **`XORTeleporter`**: A mechanism to escape local minima by generating new candidate paths via the XOR of two existing diverse paths. This is crucial for navigating the "phase transition" zone.

## Theoretical Background

The design is inspired by several concepts:

1.  **Viterbi Algorithm**: For finding the most likely path in a trellis, adapted here to minimize conflict energy.
2.  **Beam Search**: A heuristic search that keeps only the top `K` candidates to manage complexity.
3.  **Algebraic Normal Form (ANF) / Zhegalkin Polynomials**: Used to represent Boolean functions as XOR of ANDs, allowing for efficient linear algebra over GF(2).
4.  **Hamming Balls**: The search space is viewed as a set of overlapping Hamming balls. The `EntropyController` estimates the ball's volume via the `∑P(t)²` integral.
5.  **Phase Transition in 3-SAT**: The `XORTeleporter` is specifically designed to handle the hard instances near the phase transition (clause/variable ratio ≈ 4.26).

## Usage

The solver is designed to be used as a module. A typical workflow:

```python
from ebs import PQPlanner, ViterbiCore, EntropyController

# Assume 'cnf_formula' is your parsed CNF.
planner = PQPlanner(cnf_formula)
elimination_order = planner.compute_elimination_order()

viterbi = ViterbiCore(cnf_formula, elimination_order, beam_size=10)
controller = EntropyController()

viterbi.initialize_paths()
for var_idx in range(len(elimination_order)):
    paths = viterbi.beam_search_step(var_idx)
    beam_size, diversity = controller.update(paths)
    viterbi.beam_size = beam_size
    # ... (check for solution, teleport if stuck)
```
For a complete example, see the experimental scripts in the /research folder.

---

## References

The implementation directly references concepts from:

- The main PQ-Algorithm paper.
- R. Bryant, "Graph-Based Algorithms for Boolean Function Manipulation", 1986 (for BDDs and ANF).
- T. Cover, J. Thomas, "Elements of Information Theory", 2006 (for entropy and volume concepts).
- Research on phase transitions in random 3-SAT (e.g., works by Selman, Kirkpatrick, etc.).

---

## Future Work

Fully integrate the XORTeleporter with the entropy controller to automate escape from local minima.

Implement a graphical visualizer for the beam's "energy landscape".

Explore using the EBS core as a CDCL branching heuristic.
