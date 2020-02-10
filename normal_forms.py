def to_nnf(f):
    return f

def to_cnf(f):
    pass

def to_tseitin_normal_form(f):
    f = to_nnf(f)
    return to_cnf(f)
