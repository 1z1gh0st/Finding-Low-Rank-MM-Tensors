# TODO:
#   - TEST      | Run for long time on harder instance

import time
from datetime import datetime
from z3 import *
from functools import reduce

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

def init_variables():
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

def init_brent_equations():
    # Create and add boolean formula for each of the equations
    for i1, i2 in nm_pairs:
        for j1, j2 in mp_pairs:
            for k1, k2 in np_pairs:

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

                # Add equation to solver
                solver.add(lhs == rhs)

def add_lexicographic_constraint():
    for l in range(0, r-1):
        vector_l = []
        vector_l_plus_one = []
        for i1, i2 in nm_pairs:
            vector_l.append(variables[f'a{i1}{i2}^{l}'])
            vector_l_plus_one.append(variables[f'a{i1}{i2}^{l+1}'])
        for j1, j2 in mp_pairs:
            vector_l.append(variables[f'b{j1}{j2}^{l}'])
            vector_l_plus_one.append(variables[f'b{j1}{j2}^{l+1}'])
        solver.add(in_order(vector_l, vector_l_plus_one))

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

def add_sign_symmetries():
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

def add_valid_inequalities():
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
    valid_quadruples = get_valid_quadruples()
    for i1, i2, j1, j2 in valid_quadruples:
        sum_abs = Abs(variables[f'a{i1}{i2}^0'] * variables[f'b{j1}{j2}^0'])
        for l in range(1, r):
            sum_abs += Abs(variables[f'a{i1}{i2}^{l}'] * variables[f'b{j1}{j2}^{l}'])
        solver.add(sum_abs >= 1)

def get_valid_quadruples():
    valid_quadruples = []
    for i in range(0, n):
        for j in range(0, p):
            # C[i][j] = <A[i,:],B[:,j]>
            for k in range(0, m):
                # SUM += A[i,k] * B[k,j]
                valid_quadruples.append((i, k, k, j))
    return valid_quadruples

def get_dimensions():
    n = int(input('Enter dimension <n> : '))
    m = int(input('Enter dimension <m> : '))
    p = int(input('Enter dimension <p> : '))
    r = int(input('Enter max rank  <r> : '))
    print(f'Solving for: R(<{n},{m},{p}>) <= {r}')
    return n, m, p, r

n, m, p, r = get_dimensions()
nm_pairs = [(i,j) for i in range(0, n) for j in range(0, m)]
mp_pairs = [(j,k) for j in range(0, m) for k in range(0, p)]
np_pairs = [(i,k) for i in range(0, n) for k in range(0, p)]

# Create a Z3 solver instance
solver = Solver()

# Create a dictionary to hold your variables, and an array of all the variables
variables = {}
var_names = []

init_variables()
init_brent_equations()

lexicographic = True
if lexicographic:
    add_lexicographic_constraint()

sign_symmetry = True
if sign_symmetry:
    add_sign_symmetries()

valid_ineq = True
if valid_ineq:
    add_valid_inequalities()

# Start timer
t0 = time.time()

# See what is happening
set_option(verbose = 10)

# Run solver
result = solver.check()

# Print if its satisfiable
print(result)

# Record end time
t1 = time.time()
delta_t = t1 - t0
print('Δt: {} seconds\n'.format(delta_t))

# Record results here
line_to_add = f'[0,1], {n}, {m}, {p}, {r}, lexicographicOn={lexicographic}, symmytriesOn={sign_symmetry}, inequalitiesOn={valid_ineq}, {result}, {delta_t}s\n'
with open("results.txt", "a") as file:
    file.write(line_to_add)
