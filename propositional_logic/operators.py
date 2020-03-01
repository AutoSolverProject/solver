# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositional_logic/operators.py

"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from propositional_logic.syntax import *
from propositional_logic.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    sub_dict = {'->': Formula.parse('(~p|q)'), '<->': Formula.parse('((p&q)|(~p&~q))'),
                '-|': Formula.parse('~(p|q)'), '-&': Formula.parse('~(p&q)'),
                '+': Formula.parse('((p&~q)|(~p&q))'), 'T': Formula.parse('(~p|p)'),
                'F': Formula.parse('(~p&p)')}
    return formula.substitute_operators(sub_dict)

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    sub_dict = {'->': Formula.parse('~(p&~q)'), '<->': Formula.parse('~(~(p&q)&~(~p&~q))'),
                '-|': Formula.parse('(~p&~q)'), '-&': Formula.parse('~(p&q)'),
                '+': Formula.parse('~(~(p&~q)&~(~p&q))'), 'T': Formula.parse('~(~p&p)'),
                'F': Formula.parse('(~p&p)'), '|': Formula.parse('~(~p&~q)')}
    return formula.substitute_operators(sub_dict)

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    sub_dict = {'->': Formula.parse('(p-&(p-&q))'), '<->': Formula.parse('((p-&q)-&((p-&p)-&(q-&q)))'),
                '-|': Formula.parse('(((p-&p)-&(q-&q))-&((p-&p)-&(q-&q)))'), '&': Formula.parse('((p-&q)-&(p-&q))'),
                '+': Formula.parse('(((p-&p)-&q)-&(p-&(q-&q)))'), 'T': Formula.parse('(p-&(p-&p))'),
                'F': Formula.parse('((p-&(p-&p))-&(p-&(p-&p)))'), '|': Formula.parse('((p-&p)-&(q-&q))'),
                '~': Formula.parse('(p-&p)')}
    return formula.substitute_operators(sub_dict)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    sub_dict = {'&': Formula.parse('~(p->~q)'), '|': Formula.parse('(~p->q)'),
                 '+': Formula.parse('~((~p->q)->~(p->~q))'),
                 '-|': Formula.parse('~(~p->q)'),
                 '-&': Formula.parse('(p->~q)'),
                 '<->': Formula.parse('((~p->q)->~(p->~q))'),
                 'F': Formula.parse('~(p->p)'),
                 'T': Formula.parse('(p->p)')}
    return formula.substitute_operators(sub_dict)

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    sub_dict = {'&': Formula.parse('((p->(q->F))->F)'), '|': Formula.parse('((p->F)->q)'),
                 '+': Formula.parse('((((p->F)->q)->((p->(q->F))->F))->F)'),
                 '-|': Formula.parse('(((p->F)->q)->F)'),
                 '-&': Formula.parse('(p->(q->F))'),
                 '<->': Formula.parse("(((p->F)->q)->((p->(q->F))->F))"),
                 '~': Formula.parse('(p->F)'),
                 'T': Formula.parse('(F->p)')}
    return formula.substitute_operators(sub_dict)
