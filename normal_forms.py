from propositional_logic.syntax import *


def to_nnf(f):
    f = eliminate_iffs(f)
    f = eliminate_implies(f)
    f = push_negation_in(f)
    f = eliminate_double_negation(f)
    return f


def to_cnf(f):
    root = f.root
    if is_variable(root) or is_constant(root):
        return f
    f = to_nnf(f)
    if is_unary(f.root):
        return f
    if not contains_and(f):
        return f
    return to_cnf_from_nnf(f)


def eliminate_iffs(f):
    root = f.root
    if is_variable(root) or is_constant(root):
        return f
    elif is_unary(root):
        return Formula(root, eliminate_iffs(f.first))
    else:
        a, b = f.first, f.second
        if root == '<->':
            first = Formula('->', a, b)
            second = Formula('->', b, a)
            return Formula('&', first, second)
        else:
            return Formula(root, eliminate_iffs(a), eliminate_iffs(b))


def eliminate_implies(f):
    root = f.root
    if is_variable(root) or is_constant(root):
        return f
    elif is_unary(root):
        return Formula(root, eliminate_implies(f.first))
    else:
        a, b = f.first, f.second
        if root == '->':
            first = Formula('~', eliminate_implies(a))
            second = eliminate_implies(b)
            return Formula('|', first, second)
        else:
            return Formula(root, eliminate_implies(a), eliminate_implies(b))


def push_negation_in(f):
    root = f.root
    if is_variable(root) or is_constant(root):
        return f
    elif is_binary(root):
        return Formula(root, push_negation_in(f.first), push_negation_in(f.second))
    elif is_unary(root) and (is_variable(f.first.root) or is_constant(f.first.root)):
        return f
    else:
        if is_unary(f.first.root):
            return push_negation_in(eliminate_double_negation(f))
        else:
            a, b = f.first.first, f.first.second
            a, b = Formula('~', a), Formula('~', b)
            froot = f.first.root
            if froot == '&':
                froot = '|'
            else:
                froot = '&'
            return Formula(froot, push_negation_in(a), push_negation_in(b))


def eliminate_double_negation(f):
    root = f.root
    if is_variable(root) or is_constant(root):
        return f
    elif is_binary(root):
        a, b = f.first, f.second
        return Formula(root, eliminate_double_negation(a), eliminate_double_negation(b))
    else:
        if is_unary(f.first.root):
            return eliminate_double_negation(f.first.first)
        else:
            return Formula('~', eliminate_double_negation(f.first))


def to_cnf_from_nnf(f):
    root = f.root
    if is_variable(root) or is_constant(root) or is_unary(root):
        return f
    a, b = f.first, f.second
    if root == '&':
        return Formula('&', to_cnf_from_nnf(a), to_cnf_from_nnf(b))
    else:
        if contains_and(f.first):
            f = to_cnf_on_left(f)
        if contains_and(f.second):
            f = to_cnf_on_right(f)
        return f


def to_cnf_on_left(f):
    a, b = f.first, f.second
    root = a.root
    if root == '|':
        return to_cnf_from_nnf(Formula('|', to_cnf_from_nnf(a), b))
    else:
        c, d = a.first, a.second
        first = Formula('|', c, b)
        second = Formula('|', d, b)
        return Formula('&', to_cnf_from_nnf(first), to_cnf_from_nnf(second))


def to_cnf_on_right(f):
    a, b = f.first, f.second
    root = b.root
    if root == '|':
        return to_cnf_from_nnf(Formula('|', a, to_cnf_from_nnf(b)))
    else:
        c, d = b.first, b.second
        first = Formula('|', a, c)
        second = Formula('|', a, d)
        return Formula('&', to_cnf_from_nnf(first), to_cnf_from_nnf(second))


def contains_and(f):
    root = f.root
    if is_variable(root) or is_constant(root) or is_unary(root):
        return False
    if root == '&':
        return True
    else:
        return contains_and(f.first) or contains_and(f.second)

