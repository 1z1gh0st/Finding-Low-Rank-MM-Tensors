from z3 import *
import math

# Initialize dimension
n = 2, m = 2, p = 2

# Initialize maximum rank decomposition we search for
r = 7

# Define the Kronecker delta
def kron(int: i, int: j) -> int:
    if (i==j):
        return 1
    else:
        return 0

init_test()

# Initialize solver
s = Solver()

a = [[[]*2]*2]*r
b = [[[]*2]*2]*r
c = [[[]*2]*2]*r

# Initialize all vars
for idx in range(0,r):
    for i,j in [0,1]:
        a[idx,i,j] = Bools('a_({},{})^({})'.format(i,j,idx))
        b[idx,i,j] = Bools('a_({},{})^({})'.format(i,j,idx))
        c[idx,i,j] = Bools('a_({},{})^({})'.format(i,j,idx))

