import time
from datetime import datetime
from z3 import *
from functools import reduce
from itertools import combinations

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

def exists_scheme(n, m, p, r):
    nm_pairs = [(i,j) for i in range(n) for j in range(m)]
    mp_pairs = [(i,j) for i in range(m) for j in range(p)]
    np_pairs = [(i,j) for i in range(n) for j in range(p)]
    solver = Solver()
    variables = {}
    var_names = []
    for l in range(r):
        for i1,i2 in nm_pairs:
            var_name = 'a{}{}^{}'.format(i1, i2, l)
            var = Bool(var_name)
            variables[var_name] = var
            var_names.append(var_name)
        for j1,j2 in mp_pairs:
            var_name = 'b{}{}^{}'.format(j1, j2, l)
            var = Bool(var_name)
            variables[var_name] = var
            var_names.append(var_name)
        for k1,k2 in np_pairs:
            var_name = 'c{}{}^{}'.format(k1, k2, l)
            var = Bool(var_name)
            variables[var_name] = var
            var_names.append(var_name)

    for i1,i2 in nm_pairs:
        for j1,j2 in mp_pairs:
            for k1,k2 in np_pairs:
                and_exprs = []
                for l in range(r):
                    and_exprs.append(And(variables[f'a{i1}{i2}^{l}'],
                        variables['b{}{}^{}'.format(j1, j2, l)],
                        variables['c{}{}^{}'.format(k1, k2, l)]))
                # XOR over all the and expressions
                lhs = reduce(lambda x, y: Xor(x, y), and_exprs)

                # Do the product of kronecker deltas
                rhs = kron(i2,j1)*kron(i1,k1)*kron(j2,k2)
                formula = lhs
                if rhs == 0:
                    formula = Not(lhs)
                solver.add(formula)
    t0 = time.time() # Start time
    print(f'Starting solver at time: {datetime.now()}')
    result = solver.check()
    print(f'Result: {result}')
    t1 = time.time() # End time
    t_elapsed = t1 - t0 # Delta time
    print(f'Time elapsed: {t_elapsed} seconds')
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
            print('Usage : \'cpF2.py dim1 dim2 dim3 rank_upper_bound\'')
    n = int(input('Enter dimension <n> : '))
    m = int(input('Enter dimension <m> : '))
    p = int(input('Enter dimension <p> : '))
    r = int(input('Enter max rank  <r> : '))
    return n, m, p, r

def main():
    n, m, p, r = get_args()
    exists_scheme(n, m, p, r)

if __name__ == "__main__":
    main()
