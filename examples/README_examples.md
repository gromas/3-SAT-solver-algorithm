# Example 3-SAT Formulas

This directory contains example 3-SAT formulas in DIMACS CNF format.

## Files

### `example_sat.cnf`
A simple satisfiable formula:
- Variables: 3
- Clauses: 3
- Formula: (x1 ∨ x2 ∨ x3) ∧ (¬x1 ∨ ¬x2 ∨ x3) ∧ (x1 ∨ ¬x2 ∨ ¬x3)

### `example_unsat.cnf`
A simple unsatisfiable formula:
- Variables: 1
- Clauses: 2
- Formula: (x1) ∧ (¬x1) encoded with repeated literals

## Using the Examples

To test the solver with these examples:

```bash
# From the root directory
python src/sat_solver.py
# The solver includes these examples in its main function

# Or using the utility functions
from src.utils import parse_dimacs_cnf
formula = parse_dimacs_cnf('examples/example_sat.cnf')
