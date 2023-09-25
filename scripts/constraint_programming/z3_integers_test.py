# TODO:
#   - FEATURE   | Add last constraint
#   - TEST      | Run for long time on harder instance
#   - BUG       | Look into the sums that look as follows:
#       ...+
#       ...+
#       ...

import time
from datetime import datetime
from z3 import *
from functools import reduce

now = datetime.now()
output_per_line = 7
debug_on = False
f = open('log.txt', 'w')

def get_var(char, subscript1, subscript2, superscript):
    return variables[f'{char}{subscript1}{subscript2}^{superscript}']

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

print(f'Solving for: R(<{n},{m},{p}>) <= {r} with coefficients {-1, 0, 1}.')

nm_pairs = [(i,j) for i in range(0, n) for j in range(0, m)]
mp_pairs = [(j,k) for j in range(0, m) for k in range(0, p)]
np_pairs = [(i,k) for i in range(0, n) for k in range(0, p)]

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
for idx in range(0, r):

    # Initialize alphas
    for i1, i2 in nm_pairs:
        var_name = f'a{i1}{i2}^{idx}'
        var = Int(var_name)
        solver.add(Or(var == -1, var == 0, var == 1))
        variables[var_name] = var
        var_names.append(var_name)

    # Initialize betas
    for j1, j2 in mp_pairs:
        var_name = f'b{j1}{j2}^{idx}'
        var = Int(var_name)
        solver.add(Or(var == -1, var == 0, var == 1))
        variables[var_name] = var
        var_names.append(var_name)

    # Initialize gammas
    for k1, k2 in np_pairs:
        var_name = f'c{k1}{k2}^{idx}'
        var = Int(var_name)
        solver.add(Or(var == -1, var == 0, var == 1))
        variables[var_name] = var
        var_names.append(var_name)

log('variables initialized!')
# log(var_names)
# Create and add boolean formula for each of the equations
for i1, i2 in nm_pairs:
    for j1, j2 in mp_pairs:
        for k1, k2 in np_pairs:
            log('i1: {}, i2: {}, j1: {}, j2: {}, k1: {}, k2: {}'.format(i1, i2, j1, j2, k1, k2))

            # Generate expression
            prod_exprs = []
            for idx in range(0, r):
                prod_exprs.append(
                    variables['a{}{}^{}'.format(i1, i2, idx)] *
                    variables['b{}{}^{}'.format(j1, j2, idx)] *
                    variables['c{}{}^{}'.format(k1, k2, idx)])

            # Sum the products
            lhs = sum(prod_exprs)

            # Do the product of kronecker deltas
            rhs = kron(i2, j1) * kron(i1, k1) * kron(j2, k2)

            log('lhs: {}, rhs: {}'.format(lhs, rhs))

            # Add equation to solver
            solver.add(lhs == rhs)

# Sign symmetry
sign_symmetry = True
if sign_symmetry:
    print('adding sign symmetries...')
    for l in range(0, r):

        # Ensure first var is not +1
        solver.add(variables[f'a00^{0}'] <= 0)

        # Ensure that the first nonzero var is -1
        for idx_outer, (i1, i2) in enumerate(nm_pairs):

            # Redundant case, ruled out
            if (i1, i2) != (0, 0):

                # Init sum
                sum_abs = Abs(variables[f'a00^{l}'])

                # Nested loop from 1 to outer index
                for idx_inner, (i1p, i2p) in enumerate(nm_pairs[1:idx_outer]):
                    sum_abs += Abs(variables[f'a{i1p}{i2p}^{l}'])
                solver.add(variables[f'a{i1}{i2}^{l}'] <= sum_abs)

        # Ensure first var is not +1
        solver.add(variables[f'c00^{0}'] <= 0)

        # Ensure that the first nonzero var is -1
        for idx_outer, (i1, i2) in enumerate(nm_pairs):

            # Redundant case, ruled out
            if (i1, i2) != (0, 0):

                # Init sum
                sum_abs = Abs(variables[f'c00^{l}'])

                # Nested loop from 1 to outer index
                for idx_inner, (i1p, i2p) in enumerate(nm_pairs[1:idx_outer]):
                    sum_abs += Abs(variables[f'c{i1p}{i2p}^{l}'])
                solver.add(variables[f'c{i1}{i2}^{l}'] <= sum_abs)

# Valid inequalities
valid_ineq = True
if valid_ineq:
    print('adding valid inequalities...')

    # 8
    for l in range(0, r):
        sum_abs = Abs(variables[f'c00^{l}'])
        for k1, k2 in np_pairs:
            if (k1, k2) != (0, 0):
                sum_abs += Abs(variables[f'c{k1}{k2}^{l}'])
        solver.add(sum_abs >= 1)
        print(sum_abs)

    # 9
    for k1, k2 in np_pairs:
        sum_abs = Abs(variables[f'c{k1}{k2}^0'])
        for l in range(1, r):
            sum_abs += Abs(variables[f'c{k1}{k2}^{l}'])
        solver.add(sum_abs >= m)
        print(sum_abs)

    # 10
    for k1a, k2a in np_pairs:
        for k1b, k2b in np_pairs:
            if (k1a, k2a) != (k1b, k2b):
                sum_abs = Abs(variables[f'c{k1a}{k2a}^0'] - variables[f'c{k1b}{k2b}^0'])
                for l in range(1, r):
                    sum_abs += Abs(variables[f'c{k1a}{k2a}^{l}'] - variables[f'c{k1b}{k2b}^{l}'])
                solver.add(sum_abs >= 2)
                print(sum_abs)

    # 11
    for i1, i2 in nm_pairs:
        sum_abs = Abs(variables[f'a{i1}{i2}^0'])
        for l in range(1, r):
            sum_abs += Abs(variables[f'a{i1}{i2}^{l}'])
        solver.add(sum_abs >= 1)

    # 12
    for j1, j2 in mp_pairs:
        sum_abs = Abs(variables[f'b{j1}{j2}^0'])
        for l in range(1, r):
            sum_abs += Abs(variables[f'b{j1}{j2}^{l}'])
        solver.add(sum_abs >= 1)

    # 13
    # TODO: implement this one

# Start timer
t0 = time.time()

# Check if there's a satisfying assignment
plog('starting solver at time: {}...'.format(now.strftime('%H:%M:%S')))

# See what is happening
set_option(verbose = 1)

# Run solver
result = solver.check()

# Print if its satisfiable
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

# R(<2,2,2>) <= 6
# valid ineq ON = 275s
# valid ineq OFF = 275s
