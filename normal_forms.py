from propositional_logic.syntax import *
from test_utils import *


normal_forms_DEBUG = test_utils_DEBUG


def to_nnf(formula, debug=normal_forms_DEBUG):
    no_iffs = eliminate_iffs(formula)
    no_implies = eliminate_implies(no_iffs)
    pushed_negation_in = push_negation_in(no_implies)
    eliminated_double_negation = eliminate_double_negation(pushed_negation_in)

    if debug:
        assert test_is_nnf(eliminated_double_negation)

    return eliminated_double_negation


def to_cnf(formula, debug=normal_forms_DEBUG):
    root = formula.root
    if is_variable(root) or is_constant(root):
        in_cnf_form = formula

    else:
        in_nnf_form = to_nnf(formula)

        if is_unary(in_nnf_form.root):  # in_nnf_form.first in either a variable or a constant
            in_cnf_form = in_nnf_form
        elif not contains_and(formula):
            in_cnf_form = in_nnf_form
        else:
            in_cnf_form = to_cnf_from_nnf(formula)

    if debug:
        assert test_is_cnf(in_cnf_form)

    return in_cnf_form


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


def to_cnf_from_nnf(formula):
    # ￿TODO: check!
    root = formula.root
    if is_variable(root) or is_constant(root) or is_unary(root):
        return formula

    a, b = formula.first, formula.second
    if root == '&':
        return Formula('&', to_cnf_from_nnf(a), to_cnf_from_nnf(b))
    else:
        if contains_and(formula.first):
            formula = to_cnf_on_left(formula)
        if contains_and(formula.second):
            formula = to_cnf_on_right(formula)
        return formula


def to_cnf_on_left(formula):
    # ￿TODO: check!
    a, b = formula.first, formula.second
    root = a.root
    if root == '|':
        return to_cnf_from_nnf(Formula('|', to_cnf_from_nnf(a), b))
    else:
        c, d = a.first, a.second
        first = Formula('|', c, b)
        second = Formula('|', d, b)
        return Formula('&', to_cnf_from_nnf(first), to_cnf_from_nnf(second))


def to_cnf_on_right(formula):
    # ￿TODO: check!
    a, b = formula.first, formula.second
    root = b.root
    if root == '|':
        return to_cnf_from_nnf(Formula('|', a, to_cnf_from_nnf(b)))
    else:
        c, d = b.first, b.second
        first = Formula('|', a, c)
        second = Formula('|', a, d)
        return Formula('&', to_cnf_from_nnf(first), to_cnf_from_nnf(second))


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
        return not is_unary(sub_formula.root) or is_variable(sub_formula.first.root)

    return assert_on_all_sub_formulae(formula, is_nnf_helper)


def test_is_cnf(formula):
    return True  # TODO: complete!


# endregion
