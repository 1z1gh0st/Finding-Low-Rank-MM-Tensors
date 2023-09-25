from z3 import *
import numpy as np

# TODO: test functions

def abs(x):
    return If(x >= 0,x,-x)

def flatten_index(i, j, row_length):
    return (i * row_length) + j

def unflatten_index(index, row_length):
    j = index % row_length
    i = index // row_length
    return i, j

def get_mm_tensor(n, m, p):
    shape = (n * m, m * p, n * p)
    result = np.zeros(shape)
    for i in range(0, n * m):
        for j in range(0, m * p):
            for k in range(0, n * p):
                a_row, a_col = unflatten_index(i, m)
                b_row, b_col = unflatten_index(j, p)
                c_row, c_col = unflatten_index(k, p)
                if a_row == c_row and c_col == b_col:
                    result[i,j,k] = 1
                else:
                    result[i,j,k] = 0
    return result

def create_variable_matrix(n, m, name, tp):
    array = []
    abs_array = []
    for i in range(0, n):
        row = []
        abs_row = []
        for j in range(0, m):
            var_name = f'{name}_{i}{j}'
            var = Int(var_name)
            abs_var = Int('abs_' + var_name)

            row.append(var)
            abs_row.append(abs_var)
            # solver.add(var)
            constraint = Or(var == -1, var == 0, var == 1)
            abs_constraint = And(Or(abs_var == var, abs_var == -var), abs_var >= 0)
            solver.add(constraint)
            solver.add(abs_constraint)
        array.append(row)
        abs_array.append(abs_row)
    return array, abs_array

def get_factor_matrices(n, m, p, r):
    u, abs_u = create_variable_matrix(n * m, r, 'u', 'int')
    v, abs_v = create_variable_matrix(m * p, r, 'v', 'int')
    w, abs_w = create_variable_matrix(n * p, r, 'w', 'int')
    return u, abs_u, v, abs_v, w, abs_w

def valid_mm_scheme_constraint():
    for i in range(0, n):
        for j in range(0, m):
            for k in range(0, p):
                sum = u[i][0] * v[j][0] * w[k][0]
                for l in range(1, r):
                    sum += u[i][l] * v[j][l] * w[k][l]
                solver.add(sum == t[i][j][k])

def sign_symmetry():
    for l in range(0, r):
        solver.add(u[0][l] <= 0)
        for i in range(0, n * m):
            sum = abs_u[0][l]
            for i_prime in range(1, i - 1):
                sum += abs_u[i_prime][l]
            solver.add(u[i][l] <= sum)
        solver.add(w[0][l] <= 0)
        for k in range(0, n * p):
            sum = abs_w[0][l]
            for k_prime in range(1, k - 1):
                sum += abs_w[k_prime][l]
            solver.add(w[k][l] <= sum)

def valid_inequalities():
    for l in range(0, r):
        sum = abs_w[0][l]
        for k in range(1, n * p):
            sum += abs_w[k][l]
        solver.add(sum >= 1)

    for k in range(0, n * p):
        sum = abs_w[k][0]
        for l in range(1, r):
            sum += abs_w[k][l]
        solver.add(sum >= m)

    for k in range(0, n * p):
        for k_prime in range(0, n * p):
            if k != k_prime:
                sum = abs_w[k][0] - w[k_prime][0]
                for l in range(1, r):
                    sum += abs_w[k][l] - w[k_prime][l]
                solver.add(sum >= 2)

    for i in range(0, n * m):
        sum = abs_u[i][0]
        for l in range(1, r):
            sum += abs_u[i][l]
        solver.add(sum >= 1)

    for j in range(0, m * p):
        sum = abs_v[j][0]
        for l in range(1, r):
            sum += abs_v[j][l]
        solver.add(sum >= 1)

solver = Solver()
n = 2
m = 2
p = 2
r = 2
tp = 'int'
t = get_mm_tensor(n, m, p)
print(t)
u, abs_u, v, abs_v, w, abs_w = get_factor_matrices(n, m, p, r)
print(u)
print(v)
print(w)
valid_mm_scheme_constraint()
# sign_symmetry()
# valid_inequalities()

for constraint in solver.assertions():
    print(constraint)
# verbose = 10
print(solver.check())
