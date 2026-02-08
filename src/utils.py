"""
Utility functions for 3-SAT formula processing.
"""

def parse_dimacs_cnf(filename: str) -> List[Tuple[int, int, int]]:
    """
    Parse a DIMACS CNF file into a list of clauses.
    
    Args:
        filename: Path to the DIMACS CNF file
        
    Returns:
        List of clauses, each clause is a tuple of 3 integers
    """
    clauses = []
    
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            
            # Skip comments and empty lines
            if not line or line.startswith('c') or line.startswith('p'):
                continue
            
            # Parse clause line
            literals = list(map(int, line.split()))
            if literals[-1] != 0:
                raise ValueError("Clause line must end with 0")
            
            literals = literals[:-1]  # Remove trailing 0
            
            # Ensure exactly 3 literals per clause (pad if necessary)
            while len(literals) < 3:
                literals.append(literals[0] if literals else 1)
            
            clauses.append(tuple(literals[:3]))
    
    return clauses


def generate_random_3sat(num_vars: int, num_clauses: int, seed: int = None) -> List[Tuple[int, int, int]]:
    """
    Generate a random 3-SAT formula.
    
    Args:
        num_vars: Number of variables
        num_clauses: Number of clauses
        seed: Random seed for reproducibility
        
    Returns:
        Random 3-SAT formula
    """
    import random
    if seed is not None:
        random.seed(seed)
    
    formula = []
    for _ in range(num_clauses):
        # Select 3 distinct variables
        vars_selected = random.sample(range(1, num_vars + 1), 3)
        
        # Randomly negate each variable
        clause = []
        for var in vars_selected:
            if random.random() > 0.5:
                clause.append(var)
            else:
                clause.append(-var)
        
        formula.append(tuple(clause))
    
    return formula


def verify_assignment(formula: List[Tuple[int, int, int]], 
                      assignment: Dict[int, int]) -> bool:
    """
    Verify if an assignment satisfies a 3-SAT formula.
    
    Args:
        formula: 3-SAT formula
        assignment: Dictionary mapping variables to 0/1 values
        
    Returns:
        True if the assignment satisfies all clauses, False otherwise
    """
    for clause in formula:
        clause_satisfied = False
        
        for lit in clause:
            var = abs(lit)
            value = assignment.get(var, 0)
            
            if (lit > 0 and value == 1) or (lit < 0 and value == 0):
                clause_satisfied = True
                break
        
        if not clause_satisfied:
            return False
    
    return True
