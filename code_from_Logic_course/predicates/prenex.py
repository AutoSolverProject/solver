# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    root = formula.root
    if is_quantifier(root):
        return False
    elif is_binary(root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    elif is_unary(root):
        return is_quantifier_free(formula.first)
    else:
        return True

def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)
    else:
        return is_quantifier_free(formula)

def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))

def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)

def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5
    free = formula.free_variables()
    if is_quantifier_free(formula) or has_uniquely_named_variables(formula):
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    return unique_renaming_helper(formula)


def unique_renaming_helper(formula: Formula)-> \
        Tuple[Formula, Proof]:
    root = formula.root
    if is_equality(root) or is_relation(root):
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    elif is_unary(root):
        uniquely_named_formula, equivalency_proof = unique_renaming_helper(formula.first)
        uniquely_named_formula = Formula('~', uniquely_named_formula)
        equivalence_formula = equivalence_of(formula, uniquely_named_formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        step_1 = prover.add_proof(equivalency_proof.conclusion, equivalency_proof)
        prover.add_tautological_implication(equivalence_formula, {step_1})
        return uniquely_named_formula, prover.qed()
    elif is_binary(root):
        uniquely_named_first, first_equivalency_proof = \
            unique_renaming_helper(formula.first)
        uniquely_named_second, second_equivalency_proof = \
            unique_renaming_helper(formula.second)
        uniquely_named_formula = Formula(formula.root, uniquely_named_first,
                                         uniquely_named_second)
        equivalence_formula = equivalence_of(formula, uniquely_named_formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        step_1 = prover.add_proof(first_equivalency_proof.conclusion,
                                  first_equivalency_proof)
        step_2 = prover.add_proof(second_equivalency_proof.conclusion,
                                  second_equivalency_proof)
        prover.add_tautological_implication(equivalence_formula, {step_1, step_2})
        return uniquely_named_formula, prover.qed()
    else:
        unique_variable = next(fresh_variable_name_generator)
        uniquely_named_formula, equivalency_proof = \
            unique_renaming_helper(formula.predicate)
        uniquely_named_formula = uniquely_named_formula.substitute(
            {formula.variable: Term(unique_variable)})
        quantified_uniquely_named_formula = \
            Formula(formula.root, unique_variable, uniquely_named_formula)
        equivalence_formula = equivalence_of(formula, quantified_uniquely_named_formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        step_1 = prover.add_proof(equivalency_proof.conclusion, equivalency_proof)
        if formula.root == 'A':
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        else:
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        variable = formula.variable
        step_2 = prover.add_instantiated_assumption(
            Formula('->', equivalency_proof.conclusion, equivalence_formula),
            schema, {'x': variable, 'y': unique_variable,
                     'R': formula.predicate.substitute({variable: Term('_')}),
                     'Q': uniquely_named_formula.substitute({unique_variable: Term('_')})})
        prover.add_mp(equivalence_formula, step_1, step_2)
        return quantified_uniquely_named_formula, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    if not is_quantifier(formula.first.root):
        equivalence_formula = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        prover.add_tautology(equivalence_formula)
        return formula, prover.qed()
    not_predicate = Formula('~', formula.first.predicate)
    prenex_predicate, equivalence_of_not_predicate_prenex_predicate_proof = \
        pull_out_quantifications_across_negation(not_predicate)
    variable = formula.first.variable
    if formula.first.root == 'A':
        root = 'E'
        schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[0]
    else:
        root = 'A'
        schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[1]

    prenex_normal_form = Formula(root, variable, prenex_predicate)
    quantified_not_predicate = Formula(root, variable, not_predicate)
    equivalence_quantified_not_predicate_prenex_predicate = \
        equivalence_of(quantified_not_predicate, prenex_normal_form)
    equivalence_formula_prenex = equivalence_of(formula, prenex_normal_form)
    equivalence_formula_quantified_not_predicate = \
        equivalence_of(formula, quantified_not_predicate)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    step_1 = prover.add_proof(
        equivalence_of_not_predicate_prenex_predicate_proof.conclusion,
        equivalence_of_not_predicate_prenex_predicate_proof)
    step_2 = prover.add_instantiated_assumption(
        Formula('->', equivalence_of(not_predicate, prenex_predicate),
                equivalence_quantified_not_predicate_prenex_predicate), schema1,
        {'x': variable, 'y': variable,
         'R': not_predicate.substitute({variable: Term('_')}),
         'Q': prenex_predicate.substitute({variable: Term('_')})})
    step_3 = prover.add_mp(equivalence_quantified_not_predicate_prenex_predicate,
                           step_1, step_2)
    step_4 = prover.add_instantiated_assumption(
        equivalence_formula_quantified_not_predicate, schema2,
        {'x': variable, 'R': formula.first.predicate.substitute({variable: Term('_')})})
    prover.add_tautological_implication(equivalence_formula_prenex, {step_4, step_3})
    return prenex_normal_form, prover.qed()

def pull_out_quantifications_from_left_across_binary_operator(formula:
                                                              Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    if not is_quantifier(formula.first.root):
        equivalence_formula = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        prover.add_tautology(equivalence_formula)
        return formula, prover.qed()
    quantifier_root, binary_root = formula.first.root, formula.root
    if quantifier_root == 'A':
        schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        if binary_root == '&':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[2]
        elif binary_root == '|':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[6]
        else:
            quantifier_root = 'E'
            schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[10]
    else:
        schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        if binary_root == '&':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[3]
        elif binary_root == '|':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[7]
        else:
            quantifier_root = 'A'
            schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[11]
    first, variable = formula.first.predicate, formula.first.variable
    inner_formula = Formula(binary_root, first, formula.second)
    inner_prenex, equivalence_inner_formula_inner_prenex_proof = \
        pull_out_quantifications_from_left_across_binary_operator(inner_formula)
    return proof_builder(formula, quantifier_root, variable, inner_prenex,
                         inner_formula, equivalence_inner_formula_inner_prenex_proof,
                         schema1, schema2, first, formula.second)
    
def pull_out_quantifications_from_right_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2
    if not is_quantifier(formula.second.root):
        equivalence_formula = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        prover.add_tautology(equivalence_formula)
        return formula, prover.qed()
    quantifier_root, binary_root = formula.second.root, formula.root
    if quantifier_root == 'A':
        schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        if binary_root == '&':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[4]
        elif binary_root == '|':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[8]
        else:
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[12]
    else:
        schema1 = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        if binary_root == '&':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[5]
        elif binary_root == '|':
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[9]
        else:
            schema2 = ADDITIONAL_QUANTIFICATION_AXIOMS[13]
    second, variable = formula.second.predicate, formula.second.variable
    inner_formula = Formula(binary_root, formula.first, second)
    inner_prenex, equivalence_inner_formula_inner_prenex_proof = \
        pull_out_quantifications_from_right_across_binary_operator(inner_formula)
    return proof_builder(formula, quantifier_root, variable, inner_prenex,
                         inner_formula, equivalence_inner_formula_inner_prenex_proof,
                         schema1, schema2, second, formula.first)

def proof_builder(formula, quantifier_root, variable, inner_prenex, inner_formula,
                  equivalence_inner_formula_inner_prenex_proof, schema1, schema2,
                  r_template, q_template):
    prenex_normal_form = Formula(quantifier_root, variable, inner_prenex)
    quantified_inner_formula = Formula(quantifier_root, variable, inner_formula)
    equivalence_formula_prenex = equivalence_of(formula, prenex_normal_form)
    equivalence_quantified_inner_formula_prenex = \
        equivalence_of(quantified_inner_formula, prenex_normal_form)
    equivalence_formula_quantified_inner_formula = \
        equivalence_of(formula, quantified_inner_formula)

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    step_1 = prover.add_proof(equivalence_inner_formula_inner_prenex_proof.conclusion,
                              equivalence_inner_formula_inner_prenex_proof)
    instance_formula = Formula('->',
                               equivalence_inner_formula_inner_prenex_proof.conclusion,
                               equivalence_quantified_inner_formula_prenex)
    step_2 = prover.add_instantiated_assumption(
        instance_formula, schema1,
        {'x': variable, 'y': variable, 'R': inner_formula.substitute({variable: Term('_')}),
         'Q': inner_prenex.substitute({variable: Term('_')})})
    step_3 = prover.add_mp(equivalence_quantified_inner_formula_prenex, step_1, step_2)
    step_4 = prover.add_instantiated_assumption(
        equivalence_formula_quantified_inner_formula, schema2,
        {'x': variable, 'R': r_template.substitute({variable: Term('_')}), 'Q': q_template})
    prover.add_tautological_implication(equivalence_formula_prenex, {step_4, step_3})
    return prenex_normal_form, prover.qed()


def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    first_prenex, equivalence_formula_first_prenex_proof = \
        pull_out_quantifications_from_left_across_binary_operator(formula)
    quantifier_list = []
    predicate = first_prenex
    while is_quantifier(predicate.root):
        quantifier_list.append((predicate.root, predicate.variable))
        predicate = predicate.predicate
    second_prenex, equivalence_predicate_second_prenex_proof = \
        pull_out_quantifications_from_right_across_binary_operator(predicate)
    prenex_normal_form = second_prenex
    for root, variable in reversed(quantifier_list):
        prenex_normal_form = Formula(root, variable, prenex_normal_form)
    equivalence_formula_prenex = equivalence_of(formula, prenex_normal_form)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    step_1 = prover.add_proof(equivalence_formula_first_prenex_proof.conclusion,
                              equivalence_formula_first_prenex_proof)
    step = prover.add_proof(equivalence_predicate_second_prenex_proof.conclusion,
                            equivalence_predicate_second_prenex_proof)
    instance_first = equivalence_predicate_second_prenex_proof.conclusion
    for root, variable in reversed(quantifier_list):
        instance_second = equivalence_of(Formula(root, variable, predicate),
                                         Formula(root, variable, second_prenex))
        instance_formula = Formula('->', instance_first, instance_second)
        if root == 'A':
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        else:
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        instantiation_step = prover.add_instantiated_assumption(
            instance_formula, schema,
            {'x': variable, 'y': variable, 'R': predicate.substitute({variable: Term('_')}),
             'Q': second_prenex.substitute({variable: Term('_')})})
        step = prover.add_mp(instance_second, step, instantiation_step)
        predicate = Formula(root, variable, predicate)
        second_prenex = Formula(root, variable, second_prenex)
        instance_first = instance_second
    prover.add_tautological_implication(equivalence_formula_prenex, {step_1, step})
    return prenex_normal_form, prover.qed()

def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9
    if is_quantifier_free(formula):
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    elif is_binary(formula.root):
        prenex_first, equivalence_first_prenex_first_proof = \
            to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        prenex_second, equivalence_second_prenex_second_proof = \
            to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        new_formula = Formula(formula.root, prenex_first, prenex_second)
        prenex_normal_form, equivalence_new_formula_prenex_proof = \
            pull_out_quantifications_across_binary_operator(new_formula)
        equivalence_formula_new_formula = equivalence_of(formula, new_formula)
        equivalence_formula_prenex = equivalence_of(formula, prenex_normal_form)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        step_1 = prover.add_proof(equivalence_first_prenex_first_proof.conclusion,
                                  equivalence_first_prenex_first_proof)
        step_2 = prover.add_proof(equivalence_second_prenex_second_proof.conclusion,
                                  equivalence_second_prenex_second_proof)
        step_3 = prover.add_tautological_implication(equivalence_formula_new_formula,
                                                   {step_1, step_2})
        step_4 = prover.add_proof(equivalence_new_formula_prenex_proof.conclusion,
                                  equivalence_new_formula_prenex_proof)
        prover.add_tautological_implication(equivalence_formula_prenex, {step_3, step_4})
        return prenex_normal_form, prover.qed()
    elif is_unary(formula.root):
        prenex_first, equivalence_first_prenex_first_proof = \
            to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        new_formula = Formula('~', prenex_first)
        prenex_normal_form, equivalence_new_formula_prenex_proof = \
            pull_out_quantifications_across_negation(new_formula)
        equivalence_formula_new_formula = equivalence_of(formula, new_formula)
        equivalence_formula_prenex = equivalence_of(formula, prenex_normal_form)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        step_1 = prover.add_proof(equivalence_first_prenex_first_proof.conclusion,
                                  equivalence_first_prenex_first_proof)
        step_2 = prover.add_tautological_implication(equivalence_formula_new_formula,
                                                   {step_1})
        step_3 = prover.add_proof(equivalence_new_formula_prenex_proof.conclusion,
                                  equivalence_new_formula_prenex_proof)
        prover.add_tautological_implication(equivalence_formula_prenex, {step_2, step_3})
        return prenex_normal_form, prover.qed()
    else:
        prenex_predicate, equivalence_predicate_prenex_predicate_proof = \
            to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)
        prenex_normal_form = Formula(formula.root, formula.variable, prenex_predicate)
        equivalence_formula_prenex = equivalence_of(formula, prenex_normal_form)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        step_1 = \
            prover.add_proof(equivalence_predicate_prenex_predicate_proof.conclusion,
                             equivalence_predicate_prenex_predicate_proof)
        instance_first = equivalence_predicate_prenex_predicate_proof.conclusion
        instance_formula = Formula('->', instance_first, equivalence_formula_prenex)
        if formula.root == 'A':
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        else:
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        variable = formula.variable
        step_2 = prover.add_instantiated_assumption(
            instance_formula, schema,
            {'x': variable, 'y': variable,
             'R': formula.predicate.substitute({variable: Term('_')}),
             'Q': prenex_predicate.substitute({variable: Term('_')})})
        prover.add_mp(equivalence_formula_prenex, step_1, step_2)
        return prenex_normal_form, prover.qed()

def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10
    if is_quantifier_free(formula):
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    uniquely_named_formula, equivalence_of_formula_unique_formula_proof = \
        uniquely_rename_quantified_variables(formula)
    prenex_normal_form_formula, equivalence_of_unique_formula_prenex_proof = \
        to_prenex_normal_form_from_uniquely_named_variables(
            uniquely_named_formula)
    equivalence_formula = equivalence_of(formula, prenex_normal_form_formula)
    prover = Prover(equivalence_of_formula_unique_formula_proof.assumptions)
    step_1 = prover.add_proof(equivalence_of_formula_unique_formula_proof.conclusion,
                              equivalence_of_formula_unique_formula_proof)
    step_2 = prover.add_proof(equivalence_of_unique_formula_prenex_proof.conclusion,
                              equivalence_of_unique_formula_prenex_proof)
    prover.add_tautological_implication(equivalence_formula, {step_1, step_2})
    return prenex_normal_form_formula, prover.qed()
