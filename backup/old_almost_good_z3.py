from z3 import *
from functools import reduce

def kron(i: int, j: int) -> int:
    if i==j:
        return 1
    else:
        return 0

# Define the dimensions and ranges
n = 2
m = 2
p = 2

# Define the max rank we desire
r = 7

# Create a Z3 solver instance
solver = Solver()

# Create a dictionary to hold your variables
variables = {}

# Use nested loops to create and initialize the boolean variables
for idx in range(1,r+1):

    # Initialize alphas
    for i1 in range(1,n+1):
        for i2 in range(1,m+1):
            var_name = 'α{}{}^{}'.format(i1,i2,idx)
            variables[var_name] = Bool(var_name)

    # Initialize betas
    for j1 in range(1,m+1):
        for j2 in range(1,p+1):
            var_name = 'β{}{}^{}'.format(j1,j2,idx)
            variables[var_name] = Bool(var_name)

    # Initialize gammas
    for k1 in range(1,n+1):
        for k2 in range(1,p+1):
            var_name = 'γ{}{}^{}'.format(k1,k2,idx)
            variables[var_name] = Bool(var_name)

# Create and add boolean formula for each of the equations
for i1 in range(1,n+1):
    for i2 in range(1,m+1):
        for j1 in range(1,m+1):
            for j2 in range(1,p+1):
                for k1 in range(1,n+1):
                    for k2 in range(1,p+1):

                        # Initialize array of and expressions
                        and_exprs = []
                        for idx in range(1,r+1):
                            and_exprs.append(
                                And(variables['α{}{}^{}'.format(i1,i2,idx)],
                                    variables['β{}{}^{}'.format(j1,j2,idx)],
                                    variables['γ{}{}^{}'.format(k1,k2,idx)]))
                        
                        # XOR over all the and expressions
                        lhs = reduce(lambda x, y: Xor(x, y), and_exprs)

                        # Do the product of kronecker deltas
                        rhs = kron(i2,j1)*kron(j2,k1)*kron(k2,i1)

                        # Add appropriate version of the equation to the solver
                        if rhs==1:
                            solver.add(lhs)
                        else:
                            solver.add(Not(lhs))

# Check if there's a satisfying assignment
if solver.check() == sat:
    model = solver.model()
    for var in variables:
        print('{}: {}'.format(var,model[var]))
else:
    print("No satisfying assignment found.")
