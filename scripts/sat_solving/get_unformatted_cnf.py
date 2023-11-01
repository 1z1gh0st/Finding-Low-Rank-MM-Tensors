import time
from datetime import datetime
from z3 import *
from functools import reduce
from itertools import combinations

now = datetime.now()
output_per_line = 7
debug_on = False
f = open('log.txt', 'w')

def plog(msg: str) -> None:
    print(msg)
    f.write(msg) 
    f.write('\n')

def log(msg: str) -> None:
    if debug_on: print(msg)
    f.write(msg)
    f.write('\n')

def kron(i: int, j: int) -> int:
    if i == j:
        return 1
    else:
        return 0
    
def is_atom(t):
    if not is_bool(t):
        return False
    if not is_app(t):
        return False
    k = t.decl().kind()
    if k == Z3_OP_AND or k == Z3_OP_OR or k == Z3_OP_IMPLIES:
        return False
    if k == Z3_OP_EQ and t.arg(0).is_bool():
        return False
    if k == Z3_OP_TRUE or k == Z3_OP_FALSE or k == Z3_OP_XOR or k == Z3_OP_NOT:
        return False
    return True

def atoms(fml):
    visited = set([])
    atms = set([])
    def atoms_rec(t, visited, atms):
        if t in visited:
            return
        visited |= { t }
        if is_atom(t):
            atms |= { t }
        for s in t.children():
            atoms_rec(s, visited, atms)
    atoms_rec(fml, visited, atms)
    return atms

def atom2literal(m, a):
    if is_true(m.eval(a)):
        return a
    return Not(a)
    
def implicant(atoms, s, snot):
    m = snot.model()
    lits = [atom2literal(m, a) for a in atoms]
    is_sat = s.check(lits)
    assert is_sat == unsat
    core = s.unsat_core()
    return Or([mk_not(c) for c in core])


def to_cnf(fml):
    atms = atoms(fml)
    s = Solver()
    snot = Solver()
    snot.add(Not(fml))
    s.add(fml)

    while sat == snot.check():
        clause = implicant(atms, s, snot)
        yield clause
        snot.add(clause)

def apply_tseitin(expr):
    tseitin_cnf = Tactic('tseitin-cnf')
    return tseitin_cnf(expr)

def get_sublists(lst, n):
    N = len(lst)
    result = []
    num_dels = N - n
    if num_dels < 0:
        return []
    del_combs = list(combinations(range(N), num_dels))
    for del_idxs in del_combs:
        sblst = [lst[i] for i in range(N) if i not in del_idxs]
        result.append(sblst)
    return result

def add_counting_clauses(vars, thresh):
    valid_combns = get_sublists(vars, thresh)
    for sublist in valid_combns:
        formula = And(sublist)
        print(formula)
        cnf = apply_tseitin(formula)
        print(cnf)
        for clause in cnf:
            all_clauses.append(clause)
            solver.add(clause)

def add_lexicographic_constraint():
    for l in range(r-1):
        vector_l = []
        vector_l_plus_one = []
        for i1, i2 in nm_pairs:
            vector_l.append(variables[f'α{i1+1}{i2+1}^{l+1}'])
            vector_l_plus_one.append(variables[f'α{i1+1}{i2+1}^{l+2}'])
        for j1, j2 in mp_pairs:
            vector_l.append(variables[f'β{j1+1}{j2+1}^{l+1}'])
            vector_l_plus_one.append(variables[f'β{j1+1}{j2+1}^{l+2}'])
        lex_constraint = in_order(vector_l, vector_l_plus_one)
        solver.add(lex_constraint)

# Input: two vectors of variables
def in_order(vectorA, vectorB):
    # If vectorA is empty we are definitely in_order
    if not vectorA:
        return True
    # If vectorB is empty while vectorA is not we are definitely **NOT** in_order
    if not vectorB:
        return False
    # If neither are empty, compare the first elements and recurse
    return Or(vectorA[0] < vectorB[0], And(vectorA[0] == vectorB[0], in_order(vectorA[1:], vectorB[1:])))

plog('Field : F_2')

log('recieving input...')

# Define the dimensions and ranges
n = int(input('Enter dimension <n> : '))
m = int(input('Enter dimension <m> : '))
p = int(input('Enter dimension <p> : '))

# Define the max rank we desire
r = int(input('Enter max rank  <r> : '))

log('n: {}, m: {}, p: {}, r: {}'.format(n,m,p,r))

nm_pairs = [(i,j) for i in range(n) for j in range(m)]
mp_pairs = [(i,j) for i in range(m) for j in range(p)]
np_pairs = [(i,j) for i in range(n) for j in range(p)]
log('initializing solver...')

cnf_file = open(f'unformatted_cnf_files/rank_{n}{m}{p}_leq_{r}_unformatted.txt', 'w')

# Create a Z3 solver instance
solver = Solver()
log('solver initialized!')

# Create a dictionary to hold your variables
variables = {}

# Create a list to store variable names
var_names = []

log('creating variables...')

# Use nested loops to create and initialize the boolean variables
for idx in range(1, r + 1):

    # Initialize alphas
    for i1 in range(1, n + 1):
        for i2 in range(1, m + 1):
            var_name = 'α{}{}^{}'.format(i1, i2, idx)
            var = Bool(var_name)
            variables[var_name] = var
            var_names.append(var_name)

    # Initialize betas
    for j1 in range(1, m + 1):
        for j2 in range(1, p + 1):
            var_name = 'β{}{}^{}'.format(j1, j2, idx)
            var = Bool(var_name)
            variables[var_name] = var
            var_names.append(var_name)

    # Initialize gammas
    for k1 in range(1, n + 1):
        for k2 in range(1, p + 1):
            var_name = 'γ{}{}^{}'.format(k1, k2, idx)
            var = Bool(var_name)
            variables[var_name] = var
            var_names.append(var_name)

log('variables initialized!')
# log(var_names)

all_clauses = []

# Create and add boolean formula for each of the equations
for i1 in range(1, n + 1):
    for i2 in range(1, m + 1):
        for j1 in range(1, m + 1):
            for j2 in range(1, p + 1):
                for k1 in range(1, n + 1):
                    for k2 in range(1, p + 1):
                        log('i1: {}, i2: {}, j1: {}, j2: {}, k1: {}, k2: {}'.format(i1,i2,j1,j2,k1,k2))

                        # Generate expression
                        and_exprs = []
                        for idx in range(1, r + 1):
                            and_exprs.append(And(variables['α{}{}^{}'.format(i1, i2, idx)],
                                variables['β{}{}^{}'.format(j1, j2, idx)],
                                variables['γ{}{}^{}'.format(k1, k2, idx)]))

                        # XOR over all the and expressions
                        lhs = reduce(lambda x, y: Xor(x, y), and_exprs)
                        
                        # Do the product of kronecker deltas
                        rhs = kron(i2,j1)*kron(i1,k1)*kron(j2,k2)
                        log('lhs: {}, rhs: {}'.format(lhs,rhs))
                        formula = lhs
                        if rhs == 0:
                            formula = Not(lhs)
                        goal = Goal()
                        goal.add(formula)
                        formula_cnf = apply_tseitin(formula)
                        for clause in formula_cnf:
                            all_clauses.append(clause)
                            solver.add(clause)

add_lexicographic_constraint()

# Start timer
t0 = time.time()

# Define a function to recursively print the S-expression
def print_sexpr(sexpr, level=0):
    if isinstance(sexpr, str):
        print("  " * level + sexpr)
        cnf_file.write('  ' * level + sexpr)
        cnf_file.write('\n')
    elif isinstance(sexpr, list):
        for item in sexpr:
            print_sexpr(item, level + 1)

# Print the S-expression
print_expr = input('Do you want to print? y/N:')
if print_expr in ['y', 'Y', 'yes', 'Yes', 'YES']:
    print_sexpr(solver.sexpr())

run_solver = input('Do you want to solve? y/N:')
if run_solver in ['y', 'Y', 'yes', 'Yes', 'YES']:
    result = solver.check()
    print(result)
