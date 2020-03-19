from propositional_logic.syntax import *
from utils.test_utils import *


normal_forms_DEBUG = test_utils_DEBUG


def to_nnf(formula, debug=normal_forms_DEBUG):
    no_iffs = eliminate_iffs(formula)
    no_implies = eliminate_implies(no_iffs)
    pushed_negation_in = push_negation_in(no_implies)
    eliminated_double_negation = eliminate_double_negation(pushed_negation_in)

    if debug:
        assert test_is_nnf(eliminated_double_negation)

    return eliminated_double_negation


def eliminate_iffs(formula):
    root = formula.root
    if is_variable(root) or is_constant(root):
        return formula
    elif is_unary(root):
        return Formula(root, eliminate_iffs(formula.first))
    else:
        a, b = formula.first, formula.second
        a_transformed = eliminate_iffs(a)
        b_transformed = eliminate_iffs(b)
        if root == '<->':
            first = Formula('->', a_transformed, b_transformed)
            second = Formula('->', b_transformed, a_transformed)
            return Formula('&', first, second)
        else:
            return Formula(root, a_transformed, b_transformed)


def eliminate_implies(formula):
    root = formula.root
    if is_variable(root) or is_constant(root):
        return formula
    elif is_unary(root):
        return Formula(root, eliminate_implies(formula.first))
    else:
        a, b = formula.first, formula.second
        if root == '->':
            first = Formula('~', eliminate_implies(a))
            second = eliminate_implies(b)
            return Formula('|', first, second)
        else:
            return Formula(root, eliminate_implies(a), eliminate_implies(b))


def push_negation_in(formula):
    root = formula.root
    if is_variable(root) or is_constant(root):
        return formula
    elif is_binary(root):
        return Formula(root, push_negation_in(formula.first), push_negation_in(formula.second))
    elif is_unary(root) and (is_variable(formula.first.root) or is_constant(formula.first.root)):
        return formula
    else:
        if is_unary(formula.first.root):
            return push_negation_in(eliminate_double_negation(formula))
        else:  # root is unary, and first.root is binary
            a, b = formula.first.first, formula.first.second
            a, b = Formula('~', a), Formula('~', b)
            froot = formula.first.root
            new_root = froot
            if froot == '&':
                new_root = '|'
            elif froot == '|':
                new_root = '&'
            return Formula(new_root, push_negation_in(a), push_negation_in(b))


def eliminate_double_negation(formula):
    root = formula.root
    if is_variable(root) or is_constant(root):
        return formula
    elif is_binary(root):
        a, b = formula.first, formula.second
        return Formula(root, eliminate_double_negation(a), eliminate_double_negation(b))
    else:  # root is unary
        sub_formula = eliminate_double_negation(formula.first)
        if is_unary(sub_formula.root):  # We have a double negation
            return sub_formula.first
        else:
            return Formula('~', sub_formula)


def to_cnf(formula, debug=normal_forms_DEBUG):
    if is_literal(formula):
        in_cnf_form = formula

    else:
        in_nnf_form = to_nnf(formula, debug=debug)

        if is_unary(in_nnf_form.root):  # in_nnf_form is in nnf form, so it must be a literal
            in_cnf_form = in_nnf_form
        elif not contains_and(formula):  # in_nnf_form is in nnf form, so if it has no "AND" it's just a clause
            in_cnf_form = in_nnf_form
        else:
            in_cnf_form = to_cnf_from_nnf(in_nnf_form)

    if debug:
        assert test_is_cnf(in_cnf_form)

    return in_cnf_form


def to_cnf_from_nnf(in_nnf_form):
    if is_literal(in_nnf_form):
        return in_nnf_form

    if in_nnf_form.root == '&':
        return Formula('&', to_cnf_from_nnf(in_nnf_form.first), to_cnf_from_nnf(in_nnf_form.second))
    else:  # in_nnf_form.root == '|'
        if contains_and(in_nnf_form.first):
            return to_cnf_on_left(in_nnf_form)
        else:  # contains "AND" in in_nnf_form.second
            return to_cnf_on_right(in_nnf_form)


def to_cnf_on_left(formula):
    # ￿TODO: check!
    a, b = formula.first, formula.second
    a = to_cnf_from_nnf(a)
    c, d = a.first, a.second
    first = Formula('|', c, b)
    second = Formula('|', d, b)
    return Formula('&', to_cnf_from_nnf(first), to_cnf_from_nnf(second))


def to_cnf_on_right(formula):
    # ￿TODO: check!
    a, b = formula.first, formula.second
    b = to_cnf_from_nnf(b)
    c, d = b.first, b.second
    first = Formula('|', a, c)
    second = Formula('|', a, d)
    if contains_and(c):
        first = to_cnf_on_right(first)
    if contains_and(d):
        second = to_cnf_on_right(second)
    return Formula('&', first, second)


def contains_and(formula):
    root = formula.root
    if is_variable(root) or is_constant(root):
        return False
    elif is_unary(root):
        return contains_and(formula.first)
    elif root == '&':
        return True
    else:
        return contains_and(formula.first) or contains_and(formula.second)


# region Tests


def test_is_nnf(formula):

    def is_nnf_helper(sub_formula):
        # Return True iff the sub formula is either not a negation, or a negation of a variable, which is all NNF allows.
        if is_binary(sub_formula.root):
            return sub_formula.root == '&' or sub_formula.root == '|'
        else:
            return is_literal(sub_formula.first)

    return assert_on_all_sub_formulae(formula, is_nnf_helper)


def test_is_cnf(formula):
    return True  # TODO: implement!


# endregion
