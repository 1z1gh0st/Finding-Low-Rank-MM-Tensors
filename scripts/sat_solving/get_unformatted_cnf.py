import time
from datetime import datetime
from z3 import *
from functools import reduce

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

plog('Field : F_2')

log('recieving input...')

# Define the dimensions and ranges
n = int(input('Enter dimension <n> : '))
m = int(input('Enter dimension <m> : '))
p = int(input('Enter dimension <p> : '))

# Define the max rank we desire
r = int(input('Enter max rank  <r> : '))

log('n: {}, m: {}, p: {}, r: {}'.format(n,m,p,r))

log('initializing solver...')

cnf_file = open(f'rank_{n}{m}{p}_leq_{r}_unformatted.txt', 'w')

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
print_sexpr(solver.sexpr())

# Check if there's a satisfying assignment
plog('starting solver at time: {}...'.format(now.strftime('%H:%M:%S')))
if solver.check() == sat:
    model = solver.model()
    output = ''
    counter = 0
    for var_name in var_names:
        counter += 1
        var = variables[var_name]
        int_result = -1
        if model[var] == True:
            int_result = 1
        elif model[var] == False:
            int_result = 0
        output += '{}: {}'.format(var_name, int_result)
        if counter%output_per_line == 0:
            output += '\n'
        else:
            output += ', '
    show_output = input('show output? y/N: ')
    if show_output in ['y','Y','yes','Yes','YES']: plog(output)
    else: log(output)
    sol_f = open('solution.txt', 'w')
    sol_f.write('n={}, m={}, p={}, r={}\n'.format(n,m,p,r))
    sol_f.write(output)
else:
    plog('No satisfying assignment found.')

t1 = time.time()
delta_t = t1 - t0
plog('Δt: {} seconds\n'.format(delta_t))

