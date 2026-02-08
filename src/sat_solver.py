"""
Polynomial-time 3-SAT Solver (P = NP Claim)
Implementation of the 2-CNF constraint propagation algorithm.
"""

import itertools
from typing import List, Tuple, Dict, Set, Optional

class SATSolver3CNF:
    """
    A polynomial-time algorithm for 3-SAT based on 2-CNF constraint propagation.
    
    The algorithm claims to solve 3-SAT in O(m^4) time where m is the number of clauses.
    If correct, this proves P = NP.
    """
    
    def __init__(self, formula: List[Tuple[int, int, int]]):
        """
        Initialize the solver with a 3-CNF formula.
        
        Args:
            formula: List of clauses, each clause is a tuple of 3 integers.
                    Positive integers represent variables, negative integers represent negations.
                    Example: [(1, -2, 3), (2, 3, -4)] represents (x1 ∨ ¬x2 ∨ x3) ∧ (x2 ∨ x3 ∨ ¬x4)
        """
        self.formula = formula
        self.variables = self._extract_variables()
        self.groups = []  # List of groups (each group is a tuple of 3 variables)
        self.neighbors = {}  # Adjacency list for groups
        self.A = {}  # A[group_idx] = list of allowed assignments
        self.phi = {}  # phi[group_idx][assignment] = 2-CNF formula
        
    def _extract_variables(self) -> Set[int]:
        """Extract all variables from the formula."""
        vars_set = set()
        for clause in self.formula:
            for lit in clause:
                vars_set.add(abs(lit))
        return vars_set
    
    def _initialize_groups(self):
        """
        Initialize groups from clauses.
        Each group corresponds to a clause and contains its 3 variables.
        """
        self.groups = []
        self.group_to_clause = {}
        
        for clause in self.formula:
            # Extract variables from clause
            group_vars = tuple(sorted(set(abs(lit) for lit in clause)))
            # Ensure group has exactly 3 variables (pad if necessary)
            while len(group_vars) < 3:
                # Find a variable not in the group
                for var in self.variables:
                    if var not in group_vars:
                        group_vars = group_vars + (var,)
                        break
            
            group_idx = len(self.groups)
            self.groups.append(group_vars)
            self.group_to_clause[group_idx] = clause
            
        # Build neighbor graph
        self.neighbors = {i: [] for i in range(len(self.groups))}
        for i in range(len(self.groups)):
            for j in range(i + 1, len(self.groups)):
                if set(self.groups[i]) & set(self.groups[j]):
                    self.neighbors[i].append(j)
                    self.neighbors[j].append(i)
    
    def _compute_phi(self, group_idx: int, assignment: Tuple[int, int, int]) -> List[Tuple]:
        """
        Compute Φ(a) for a given group and assignment.
        
        Args:
            group_idx: Index of the group
            assignment: Tuple of 3 binary values (0 or 1) for the group variables
            
        Returns:
            List of 2-CNF clauses, or None if contradiction found
        """
        group = self.groups[group_idx]
        assignment_dict = {group[i]: assignment[i] for i in range(3)}
        
        # Apply assignment to all clauses
        phi_clauses = []
        
        for clause in self.formula:
            # Evaluate clause under partial assignment
            clause_result = self._evaluate_clause(clause, assignment_dict)
            
            if clause_result is None:
                continue  # Clause is satisfied
            elif clause_result == []:
                return None  # Empty clause - contradiction
            elif len(clause_result) <= 2:
                phi_clauses.append(tuple(sorted(clause_result)))
        
        return phi_clauses
    
    def _evaluate_clause(self, clause: Tuple[int, int, int], 
                         assignment: Dict[int, int]) -> Optional[List[int]]:
        """
        Evaluate a clause under a partial assignment.
        
        Returns:
            - None if clause is satisfied
            - [] if clause is falsified (empty clause)
            - List of remaining literals otherwise
        """
        remaining = []
        
        for lit in clause:
            var = abs(lit)
            if var in assignment:
                # Variable is assigned
                value = assignment[var]
                if (lit > 0 and value == 1) or (lit < 0 and value == 0):
                    return None  # Clause is satisfied
                # Literal is false, don't add it
            else:
                # Variable is unassigned
                remaining.append(lit)
        
        return remaining if remaining else []
    
    def _is_2cnf_satisfiable(self, clauses: List[Tuple]) -> bool:
        """
        Check if a 2-CNF formula is satisfiable.
        
        This is a simplified implementation. For production use, 
        consider a more efficient 2-SAT algorithm.
        """
        if not clauses:
            return True
            
        # Extract all variables from clauses
        all_lits = set()
        for clause in clauses:
            for lit in clause:
                all_lits.add(abs(lit))
        
        # Brute-force check for small formulas (for demonstration)
        # In a full implementation, use implication graph algorithm
        n = len(all_lits)
        variables = list(all_lits)
        
        for i in range(2**n):
            assignment = {}
            for j, var in enumerate(variables):
                assignment[var] = (i >> j) & 1
            
            # Check all clauses
            satisfied = True
            for clause in clauses:
                clause_ok = False
                for lit in clause:
                    var = abs(lit)
                    value = assignment.get(var, 0)  # Default to 0 if not in this subset
                    if (lit > 0 and value == 1) or (lit < 0 and value == 0):
                        clause_ok = True
                        break
                
                if not clause_ok:
                    satisfied = False
                    break
            
            if satisfied:
                return True
        
        return False
    
    def solve(self) -> Tuple[str, Optional[Dict[int, int]]]:
        """
        Main algorithm to solve the 3-SAT formula.
        
        Returns:
            Tuple of (result, assignment) where:
            - result is either "SAT" or "UNSAT"
            - assignment is a dictionary of variable assignments if SAT, None otherwise
        """
        print("Initializing algorithm...")
        
        # Step 0: Initialize groups
        self._initialize_groups()
        print(f"Created {len(self.groups)} groups")
        
        # Step 0: Initialize A(G) and Φ(a)
        for i in range(len(self.groups)):
            self.A[i] = []
            self.phi[i] = {}
            
            group = self.groups[i]
            # Generate all 8 possible assignments for this group
            for bits in itertools.product([0, 1], repeat=3):
                phi_a = self._compute_phi(i, bits)
                
                if phi_a is None:  # Contradiction found
                    continue
                    
                if self._is_2cnf_satisfiable(phi_a):
                    self.A[i].append(bits)
                    self.phi[i][bits] = phi_a
        
        # Check for empty groups
        for i in range(len(self.groups)):
            if not self.A[i]:
                print(f"Group {i} has no valid assignments -> UNSAT")
                return "UNSAT", None
        
        print("Initialization complete. Starting constraint propagation...")
        
        # Step 1: Iterative refinement
        changed = True
        iteration = 0
        
        while changed:
            changed = False
            iteration += 1
            print(f"Iteration {iteration}")
            
            # Make copies for safe modification
            new_A = {i: list(self.A[i]) for i in self.A}
            new_phi = {i: dict(self.phi[i]) for i in self.phi}
            
            for i in range(len(self.groups)):
                for assignment in list(self.A[i]):
                    assignment_tuple = tuple(assignment)
                    
                    # Check all neighbor groups
                    for j in self.neighbors[i]:
                        # Find compatible assignments in group j
                        compatible_found = False
                        
                        for b_assignment in self.A[j]:
                            # Check compatibility on shared variables
                            common_vars = set(self.groups[i]) & set(self.groups[j])
                            compatible = True
                            
                            for var in common_vars:
                                idx_i = self.groups[i].index(var)
                                idx_j = self.groups[j].index(var)
                                if assignment_tuple[idx_i] != b_assignment[idx_j]:
                                    compatible = False
                                    break
                            
                            if not compatible:
                                continue
                            
                            # Check satisfiability of Φ(a) ∧ Φ(b)
                            if self._is_2cnf_satisfiable(self.phi[i][assignment_tuple] + 
                                                       self.phi[j][b_assignment]):
                                compatible_found = True
                                break
                        
                        if not compatible_found:
                            # Remove assignment a from A[i]
                            if assignment_tuple in new_A[i]:
                                new_A[i].remove(assignment_tuple)
                                if assignment_tuple in new_phi[i]:
                                    del new_phi[i][assignment_tuple]
                                changed = True
                                print(f"  Removed assignment {assignment_tuple} from group {i}")
                                break
                    
                    if changed:  # Break inner loop if assignment was removed
                        break
            
            # Update A and phi
            self.A = new_A
            self.phi = new_phi
            
            # Check for empty groups
            for i in range(len(self.groups)):
                if not self.A[i]:
                    print(f"Group {i} became empty -> UNSAT")
                    return "UNSAT", None
        
        print(f"Algorithm completed after {iteration} iterations")
        
        # Step 2: Check result
        all_non_empty = all(len(self.A[i]) > 0 for i in range(len(self.groups)))
        
        if all_non_empty:
            print("All groups have assignments -> SAT")
            # Construct a satisfying assignment
            assignment = self._construct_assignment()
            return "SAT", assignment
        else:
            print("Some group is empty -> UNSAT")
            return "UNSAT", None
    
    def _construct_assignment(self) -> Dict[int, int]:
        """
        Construct a global assignment from the remaining assignments in A(G).
        This is a heuristic approach and may need refinement.
        """
        assignment = {}
        
        # Process groups in some order
        for i in range(len(self.groups)):
            if self.A[i]:
                # Take the first assignment for this group
                bits = self.A[i][0]
                group = self.groups[i]
                
                for var_idx, var in enumerate(group):
                    if var not in assignment:
                        assignment[var] = bits[var_idx]
                    # If there's a conflict, prefer the current group's assignment
                    elif assignment[var] != bits[var_idx]:
                        assignment[var] = bits[var_idx]
        
        # Fill in any missing variables with default value
        for var in self.variables:
            if var not in assignment:
                assignment[var] = 0
        
        return assignment


def solve_3sat(formula: List[Tuple[int, int, int]]) -> Tuple[str, Optional[Dict[int, int]]]:
    """
    Convenience function to solve a 3-SAT formula.
    
    Args:
        formula: List of clauses, each with 3 literals
        
    Returns:
        Tuple of (result, assignment)
    """
    solver = SATSolver3CNF(formula)
    return solver.solve()


# Example usage
if __name__ == "__main__":
    # Example 1: Simple satisfiable formula (x1 ∨ x2 ∨ x3) ∧ (¬x1 ∨ ¬x2 ∨ ¬x3)
    formula1 = [
        (1, 2, 3),
        (-1, -2, -3)
    ]
    
    print("Testing formula 1: (x1 ∨ x2 ∨ x3) ∧ (¬x1 ∨ ¬x2 ∨ ¬x3)")
    result1, assignment1 = solve_3sat(formula1)
    print(f"Result: {result1}")
    if result1 == "SAT":
        print(f"Assignment: {assignment1}")
    print()
    
    # Example 2: Simple unsatisfiable formula (x1) ∧ (¬x1)
    formula2 = [
        (1, 1, 1),      # (x1 ∨ x1 ∨ x1) ≡ x1
        (-1, -1, -1)    # (¬x1 ∨ ¬x1 ∨ ¬x1) ≡ ¬x1
    ]
    
    print("Testing formula 2: (x1) ∧ (¬x1)")
    result2, assignment2 = solve_3sat(formula2)
    print(f"Result: {result2}")
