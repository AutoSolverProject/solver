# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositional_logic/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositional_logic.syntax import *
from propositional_logic.proofs import *
from propositional_logic.deduction import *
from propositional_logic.semantics import *
#from propositional_logic.operators import *
from propositional_logic.axiomatic_systems import *

def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a

    formulae = list()
    var_list = sorted(list(model.keys()))
    for v in var_list:
        if model[v]:
            formulae.append(Formula(v))
        else:
            formulae.append(Formula.parse('~' + v))
    return formulae

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositional_logic.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

    assumptions = formulae_capturing_model(model)
    if evaluate(formula, model):
        if is_variable(formula.root):
            return Proof(InferenceRule(assumptions, formula), AXIOMATIC_SYSTEM,
                         [Proof.Line(formula)])
        elif is_unary(formula.root):
            return prove_in_model(formula.first, model)
        elif formula.root == '->':
            if evaluate(formula.second, model):
                return prove_corollary(prove_in_model(formula.second, model), formula, I1)
            return prove_corollary(prove_in_model(formula.first, model), formula, I2)
    else:
        if is_variable(formula.root):
            return Proof(InferenceRule(assumptions, Formula('~', formula)), AXIOMATIC_SYSTEM,
                         [Proof.Line(Formula('~', formula))])
        if is_unary(formula.root):
            return prove_corollary(prove_in_model(formula.first, model),
                                   Formula('~', formula), NN)
        elif formula.root == '->':
            return combine_proofs(prove_in_model(formula.first, model),
                                  prove_in_model(formula.second, model),
                                  Formula('~', formula), NI)



def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2

    pfa_minus_last_assumption = remove_assumption(proof_from_affirmation)
    pfn_minus_last_assumption = remove_assumption(proof_from_negation)
    return combine_proofs(pfa_minus_last_assumption,
                          pfn_minus_last_assumption,
                          proof_from_affirmation.statement.conclusion,
                          R)

def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositional_logic.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a

    if len(model) == len(tautology.variables()):
        return prove_in_model(tautology, model)
    variables_set = sorted(tautology.variables())
    i = 0
    while i < len(variables_set):
        if variables_set[i] not in model.keys():
            break
        i += 1
    model_neg_last = model.copy()
    model_pos_last = model.copy()
    model_neg_last[variables_set[i]] = False
    model_pos_last[variables_set[i]] = True
    return reduce_assumption(prove_tautology(tautology, model_pos_last),
                             prove_tautology(tautology, model_neg_last))

def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositional_logic.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b

    models = all_models(formula.variables())
    for model in models:
        if not evaluate(formula, model):
            return model
    return prove_tautology(formula)

def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a

    formula = rule.conclusion
    for assumption in reversed(rule.assumptions):
        formula = Formula('->', assumption, formula)
    return formula

def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositional_logic.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b

    formula = encode_as_formula(rule)
    formula_proof = prove_tautology(formula)
    lines = list(formula_proof.lines)
    for assumption in rule.assumptions:
        last_line = len(lines) - 1
        lines.append(Proof.Line(assumption))
        left_prop = len(lines) - 1
        lines.append(Proof.Line(lines[last_line].formula.second, MP, [left_prop, last_line]))
    return Proof(rule, AXIOMATIC_SYSTEM, lines)

def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositional_logic.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5

    formulae_list = [f for f in formulae]
    variables_list = []
    for f in formulae_list:
        for v in f.variables():
            if v not in variables_list:
                variables_list.append(v)
    models = all_models(variables_list)
    for model in models:
        i = 0
        while i < len(formulae_list):
            if not evaluate(formulae_list[i], model):
                break
            i += 1
        if i == len(formulae_list):
            return model
    return prove_sound_inference(InferenceRule(formulae_list, Formula.parse('~(p->p)')))

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositional_logic.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
