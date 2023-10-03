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

plog('Ring : Z, Coefficient set : {-1,0,1}')

log('recieving input...')

# Define the dimensions and ranges
n = int(input('Enter dimension <n> : '))
m = int(input('Enter dimension <m> : '))
p = int(input('Enter dimension <p> : '))

# Define the max rank we desire
r = int(input('Enter max rank  <r> : '))

log('n: {}, m: {}, p: {}, r: {}'.format(n,m,p,r))

log('initializing solver...')

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
            var = Int(var_name)
            solver.add(Or(var == -1, var == 0, var == 1))
            variables[var_name] = var
            var_names.append(var_name)

    # Initialize betas
    for j1 in range(1, m + 1):
        for j2 in range(1, p + 1):
            var_name = 'β{}{}^{}'.format(j1, j2, idx)
            var = Int(var_name)
            solver.add(Or(var == -1, var == 0, var == 1))
            variables[var_name] = var
            var_names.append(var_name)

    # Initialize gammas
    for k1 in range(1, n + 1):
        for k2 in range(1, p + 1):
            var_name = 'γ{}{}^{}'.format(k1, k2, idx)
            var = Int(var_name)
            solver.add(Or(var == -1, var == 0, var == 1))
            variables[var_name] = var
            var_names.append(var_name)

log('variables initialized!')
# log(var_names)
# Create and add boolean formula for each of the equations
for i1 in range(1, n + 1):
    for i2 in range(1, m + 1):
        for j1 in range(1, m + 1):
            for j2 in range(1, p + 1):
                for k1 in range(1, n + 1):
                    for k2 in range(1, p + 1):
                        log('i1: {}, i2: {}, j1: {}, j2: {}, k1: {}, k2: {}'.format(i1, i2, j1, j2, k1, k2))

                        # Generate expression
                        prod_exprs = []
                        for idx in range(1, r + 1):
                            prod_exprs.append(
                                variables['α{}{}^{}'.format(i1, i2, idx)] *
                                variables['β{}{}^{}'.format(j1, j2, idx)] *
                                variables['γ{}{}^{}'.format(k1, k2, idx)])

                        # Sum the products
                        lhs = sum(prod_exprs)

                        # Do the product of kronecker deltas
                        rhs = kron(i2, j1) * kron(i1, k1) * kron(j2, k2)

                        log('lhs: {}, rhs: {}'.format(lhs,rhs))

                        # Add equation to solver
                        solver.add(lhs == rhs)

# Start timer
t0 = time.time()

# Check if there's a satisfying assignment
plog('starting solver at time: {}...'.format(now.strftime('%H:%M:%S')))
set_option(verbose = 1)
result = solver.check()
print(result)
'''

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
'''

t1 = time.time()
delta_t = t1 - t0
plog('Δt: {} seconds\n'.format(delta_t))
