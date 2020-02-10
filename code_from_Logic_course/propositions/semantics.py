# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""
from itertools import product
from typing import AbstractSet, Iterable, Iterator, List, Mapping

from tabulate import tabulate

from propositions.syntax import *
from propositions.proofs import *

Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1

    root = formula.root
    if is_variable(root):
        return model[root]
    elif is_constant(root):
        return root == 'T'
    elif is_unary(root):
        return not evaluate(formula.first, model)
    else:
        if root == '&':
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif root == '|':
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif root == '->':
            return (not evaluate(formula.first, model)) or evaluate(formula.second, model)
        elif root == '<->':
            return (evaluate(formula.first, model) and evaluate(formula.second, model)) or\
                   (not evaluate(formula.first, model) and not evaluate(formula.second, model))
        elif root == '+':
            return (evaluate(formula.first, model) and not evaluate(formula.second, model)) or \
                   (not evaluate(formula.first, model) and evaluate(formula.second, model))
        elif root == '-|':
            return not (evaluate(formula.first, model) or evaluate(formula.second, model))
        elif root == '-&':
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))


def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
        return list(dict(zip(variables, val)) for val in product({True, False}, repeat=len(variables)))


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3

    if len(formula.variables()) == 0:
        return [evaluate(formula, {})]

    return list(evaluate(formula, model) for model in models)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4

    var_list = sorted(list(formula.variables()))
    models = all_models(var_list)
    values = truth_values(formula, models)
    line1 = "| "
    i = 0
    while i < len(var_list):
        line1 += str(var_list[i]) + " | "
        i += 1
    line1 += str(formula) + " |"
    print(line1)
    line2 = "|-"
    i = 0
    while i < len(var_list):
        line2 += "-" * len(str(var_list[i])) + "-|-"
        i += 1
    line2 += "-" * len(str(formula)) + "-|"
    print(line2)
    i = 0
    for model in models:
        line = "| "
        for v in var_list:
            if model[v]:
                line += "T"
            else:
                line += "F"
            line += " " * (len(str(v)) - 1) + " | "
        if values[i]:
            line += "T"
        else:
            line += "F"
        line += " " * (len(str(formula)) - 1) + " |"
        print(line)
        i += 1


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a

    return 0 not in truth_values(formula, all_models(formula.variables()))


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b

    return 1 not in truth_values(formula, all_models(formula.variables()))


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c

    return 1 in truth_values(formula, all_models(formula.variables()))


def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    # Task 2.6

    if len(model.keys()) <= 1:
        key = list(model.keys())[0]
        return Formula(key) if model[key] else Formula('~', Formula(key))
    formula = ""
    for k in model.keys():
        if model[k]:
            if formula is "":
                formula += "(" + k + "&"
            elif formula.endswith('&'):
                formula += k + ")"
            elif formula.endswith(')'):
                formula = "(" + formula + "&" + k + ")"
        else:
            if formula is "":
                formula += "(~" + k + "&"
            elif formula.endswith('&'):
                formula += "~" + k + ")"
            elif formula.endswith(')'):
                formula = "(" + formula + "&~" + k + ")"
    return Formula.parse(formula)



def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7

    if 1 not in values:
        return Formula('&', Formula(variables[0]), Formula('~', Formula(variables[0])))
    models = all_models(variables)
    formulae = list()
    for i in range(len(models)):
        if values[i]:
            formulae.append(synthesize_for_model(models[i]))
    if len(formulae) == 1:
        return formulae[0]
    formula = formulae[0]
    for i in range(1, len(formulae)):
        formula = Formula('|', formula, formulae[i])
    return formula


# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2

    for assumption in rule.assumptions:
        if not evaluate(assumption, model):
            return True
    return evaluate(rule.conclusion, model)


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3

    vars = rule.variables()
    models = all_models(vars)
    if models is None:
        return evaluate_inference(rule, {})
    for model in models:
        if not evaluate_inference(rule, model):
            return False
    return True
