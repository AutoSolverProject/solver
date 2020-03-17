from formula_utils import *


test_utils_DEBUG = True


def assert_on_all_sub_formulae(formula, assertion_function):
    """
    A helper function to check that a certain condition hold on the entire closure of the formula.
    :param formula: the formula to check.
    :param assertion_function: the assertion function. Returns True to signify that the condition was not violated.
    :return: True iff the assertion_function returned True on <b>ALL</b> of formula's subformulae.
    """
    sub_formulae = find_closure(formula)
    return all(assertion_function(sub_formula) for sub_formula in sub_formulae)


