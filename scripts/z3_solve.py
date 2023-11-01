import time
from datetime import datetime
from z3 import *
from functools import reduce
from itertools import combinations

def in_order(vectorA, vectorB, mode):
    # If vectorA is empty we are definitely in_order
    if not vectorA:
        return True
    # If vectorB is empty while vectorA is not we are definitely **NOT** in_order
    if not vectorB:
        return False
    # If neither are empty, compare the first elements and recurse
    if mode == 'sat':
        return Or(And(Not(vectorA[0]), vectorB[0]), And(vectorA[0] == vectorB[0], in_order(vectorA[1:], vectorB[1:], mode)))
    elif mode == 'smt':
        return Or(vectorA[0] < vectorB[0], And(vectorA[0] == vectorB[0], in_order(vectorA[1:], vectorB[1:], mode)))


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

def exists_scheme(n, m, p, r, mode, coefficients):
    nm_pairs = [(i,j) for i in range(n) for j in range(m)]
    mp_pairs = [(i,j) for i in range(m) for j in range(p)]
    np_pairs = [(i,j) for i in range(n) for j in range(p)]
    solver = Solver()
    variables = {}
    var_names = []
    for l in range(r):
        def add_variable(name):
            if mode == 'sat':
                var = Bool(name)
                variables[name] = var
                var_names.append(name)
            elif mode == 'smt':
                var = Int(name)
                variables[name] = var
                var_names.append(name)
                solver.add(Or([var == x for x in coefficients]))
        for i1, i2 in nm_pairs:
            var_name = f'a{i1}{i2}^{l}'
            add_variable(var_name)
        for j1, j2 in mp_pairs:
            var_name = f'b{j1}{j2}^{l}'
            add_variable(var_name)
        for k1, k2 in np_pairs:
            var_name = f'c{k1}{k2}^{l}'
            add_variable(var_name)
    for i1, i2 in nm_pairs:
        for j1, j2 in mp_pairs:
            for k1, k2 in np_pairs:
                if mode=='sat':
                    and_exprs = []
                    for l in range(r):
                        and_exprs.append(And(variables[f'a{i1}{i2}^{l}'],
                            variables[f'b{j1}{j2}^{l}'],
                            variables[f'c{k1}{k2}^{l}']))
                    lhs = reduce(lambda x, y: Xor(x, y), and_exprs)
                    rhs = kron(i2,j1)*kron(i1,k1)*kron(j2,k2)
                    formula = lhs
                    if rhs == 0:
                        formula = Not(lhs)
                    goal = Goal()
                    goal.add(formula)
                    formula_cnf = apply_tseitin(formula)
                    for clause in formula_cnf:
                        solver.add(clause)
                elif mode=='smt':
                    prod_exprs = []
                    for idx in range(0, r):
                        prod_exprs.append(
                            variables['a{}{}^{}'.format(i1, i2, idx)] *
                            variables['b{}{}^{}'.format(j1, j2, idx)] *
                            variables['c{}{}^{}'.format(k1, k2, idx)])
                    lhs = sum(prod_exprs)
                    rhs = kron(i2, j1) * kron(i1, k1) * kron(j2, k2)
                    solver.add(lhs == rhs)
                else:
                    raise Exception(f'Invalid mode: {mode}')
    if input('Add lex constr? y/n: ') in ['y', 'Y', 'yes', 'YES', 'Yes']:
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
                if mode == 'sat':
                    cnf_lex = to_cnf(in_order(vector_l, vector_l_plus_one, mode))
                    for clause in cnf_lex:
                        solver.add(clause)
                else:
                    solver.add(in_order(vector_l, vector_l_plus_one, mode))
        add_lexicographic_constraint()
    if mode == 'smt':
        if input('Add sign sym? y/n: ') in ['y', 'Y', 'yes', 'YES', 'Yes']:
            def add_sign_symmetries():
                for i_r in range(0, r):
                    solver.add(variables[f'a00^{0}'] <= 0)
                    for idx_outer, (i1, i2) in enumerate(nm_pairs):
                        if (i1, i2) != (0, 0):
                            sum_abs = Abs(variables[f'a00^{i_r}'])
                            for idx_inner, (i1p, i2p) in enumerate(nm_pairs[1:idx_outer]):
                                sum_abs += Abs(variables[f'a{i1p}{i2p}^{i_r}'])
                            solver.add(variables[f'a{i1}{i2}^{l}'] <= sum_abs)
                    solver.add(variables[f'c00^{0}'] <= 0)
                    for idx_outer, (i1, i2) in enumerate(nm_pairs):
                        if (i1, i2) != (0, 0):
                            sum_abs = Abs(variables[f'c00^{l}'])
                            for idx_inner, (i1p, i2p) in enumerate(nm_pairs[1:idx_outer]):
                                sum_abs += Abs(variables[f'c{i1p}{i2p}^{i_r}'])
                            solver.add(variables[f'c{i1}{i2}^{l}'] <= sum_abs)
            add_sign_symmetries()
        if input('Add valid ineq? y/n: ') in ['y', 'Y', 'yes', 'YES', 'Yes']:
            def add_valid_inequalities():
                for l in range(0, r):
                    sum_abs = Abs(variables[f'c00^{l}'])
                    for k1, k2 in np_pairs:
                        if (k1, k2) != (0, 0):
                            sum_abs += Abs(variables[f'c{k1}{k2}^{l}'])
                    solver.add(sum_abs >= 1)
                for k1, k2 in np_pairs:
                    sum_abs = Abs(variables[f'c{k1}{k2}^0'])
                    for l in range(1, r):
                        sum_abs += Abs(variables[f'c{k1}{k2}^{l}'])
                    solver.add(sum_abs >= m)
                for k1a, k2a in np_pairs:
                    for k1b, k2b in np_pairs:
                        if (k1a, k2a) != (k1b, k2b):
                            sum_abs = Abs(variables[f'c{k1a}{k2a}^0'] - variables[f'c{k1b}{k2b}^0'])
                            for l in range(1, r):
                                sum_abs += Abs(variables[f'c{k1a}{k2a}^{l}'] - variables[f'c{k1b}{k2b}^{l}'])
                            solver.add(sum_abs >= 2)
                for i1, i2 in nm_pairs:
                    sum_abs = Abs(variables[f'a{i1}{i2}^0'])
                    for l in range(1, r):
                        sum_abs += Abs(variables[f'a{i1}{i2}^{l}'])
                    solver.add(sum_abs >= 1)
                for j1, j2 in mp_pairs:
                    sum_abs = Abs(variables[f'b{j1}{j2}^0'])
                    for l in range(1, r):
                        sum_abs += Abs(variables[f'b{j1}{j2}^{l}'])
                    solver.add(sum_abs >= 1)
                def get_valid_quadruples():
                    valid_quadruples = []
                    for i in range(0, n):
                        for j in range(0, p):
                            for k in range(0, m):
                                valid_quadruples.append((i, k, k, j))
                    return valid_quadruples
                valid_quadruples = get_valid_quadruples()
                for i1, i2, j1, j2 in valid_quadruples:
                    sum_abs = Abs(variables[f'a{i1}{i2}^0'] * variables[f'b{j1}{j2}^0'])
                    for l in range(1, r):
                        sum_abs += Abs(variables[f'a{i1}{i2}^{l}'] * variables[f'b{j1}{j2}^{l}'])
                    solver.add(sum_abs >= 1)
            add_valid_inequalities()

    t0 = time.time() # Start time
    now = datetime.now().strftime('%H:%M')
    print(f'Starting solver at time: {now}')
    result = solver.check()
    print(f'Result: {result}')
    t1 = time.time() # End time
    t_elapsed = t1 - t0 # Delta time
    print(f'Time elapsed: {t_elapsed} seconds')
    filename = 'results.info'
    with open(filename, 'a') as file:
        file.writelines([f'Mode: {mode} | Coef: {coefficients} | Dim: {n} {m} {p} {r} | Time: {t_elapsed}s | {result}\n'])
    return result

def get_args():
    if len(sys.argv) >= 5:
        try:
            n = int(sys.argv[1])
            m = int(sys.argv[2])
            p = int(sys.argv[3])
            r = int(sys.argv[4])
            return n, m, p, r
        except ValueError:
            print('Usage : \'python3 {sys.argv[0]} dim1 dim2 dim3 rank_upper_bound\'')
    n = int(input('Enter dimension <n> : '))
    m = int(input('Enter dimension <m> : '))
    p = int(input('Enter dimension <p> : '))
    r = int(input('Enter max rank  <r> : '))
    return n, m, p, r

def main():
    n, m, p, r = get_args()
    mode = None
    while mode!='sat' and mode!='smt':
        mode = input('What mode would you like to use? sat/smt: ')
        if mode!='sat' and mode!='smt':
            print('Invalid input.')
    if mode=='smt':
        coefficients = [int(x) for x in input('Please enter desired coefficients. For all integers press \'enter\': ').split()]
    else:
        coefficients = [0,1]
    exists_scheme(n, m, p, r, mode, coefficients)

if __name__ == "__main__":
    main()
