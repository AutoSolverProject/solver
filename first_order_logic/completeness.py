# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: first_order_logic/completeness.py

from typing import AbstractSet, Container, Set, Union

import itertools

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *

def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants

def get_relations(formulae):
    relations = set()
    for formula in formulae:
        relations.update(formula.relations())
    return relations

def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)

def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation, is one of
        the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.1
    const_set = get_constants(sentences)
    relation_set = get_relations(sentences)
    for relation, arity in relation_set:
        if arity == -1:
            continue
        terms_list = itertools.product(const_set, repeat=arity)
        for terms in terms_list:
            terms = [Term(term) for term in terms]
            formula = Formula(relation, terms)
            if formula not in sentences and Formula('~', formula) not in sentences:
                return False
    return True

def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences, ``False`` otherwise.
    """
    const_set = get_constants(sentences)
    for sentence in sentences:
        # assert is_in_prenex_normal_form(sentence) and \
        #        len(sentence.free_variables()) == 0
    # Task 12.1.2

        if sentence.root == 'A':
            for c in const_set:
                if sentence.predicate.substitute({sentence.variable: Term(c)}) \
                        not in sentences:
                    return False
    return True

def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences, ``False`` otherwise.
    """
    const_set = get_constants(sentences)
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.3
        if sentence.root == 'E':
            i = 0
            for c in const_set:
                if not sentence.predicate.substitute({sentence.variable: Term(c)}) \
                        in sentences:
                    i += 1
                else:
                    break
            if i == len(const_set):
                return False
    return True

def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    if not is_quantifier(unsatisfied.root):
        return unsatisfied
    variable = unsatisfied.variable
    unsatisfied = unsatisfied.predicate
    for c in model.universe:
        new_formula = unsatisfied.substitute({variable: Term(c)})
        if new_formula in sentences and not model.evaluate_formula(new_formula):
            return find_unsatisfied_quantifier_free_sentence(
                sentences, model, new_formula)

def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1
    if is_relation(quantifier_free.root):
        return {quantifier_free}
    elif is_unary(quantifier_free.root):
        return get_primitives(quantifier_free.first)
    return get_primitives(quantifier_free.first) | (
        get_primitives(quantifier_free.second))

def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~first_order_logic.prover.Prover.AXIOMS`.
    """    
    assert is_closed(sentences)
    # Task 12.3.2
    universe = get_constants(sentences)
    constant_meaning = {c: c for c in universe}
    relation_meaning = {}
    for relation, arity in get_relations(sentences):
        relation_meaning[relation] = set()
        if arity == -1:
            continue
        terms_list = itertools.product(universe, repeat=arity)
        for terms in terms_list:
            formula = Formula(relation, [Term(term) for term in terms])
            if formula in sentences:
                relation_meaning[relation].add(terms)
    model = Model(universe, constant_meaning, relation_meaning)
    for sentence in sentences:
        if not model.is_model_of({sentence}):
            unsatisfied = find_unsatisfied_quantifier_free_sentence(
                sentences, model, sentence)
            primitives = get_primitives(unsatisfied)
            assumptions = [unsatisfied]
            for primitive in primitives:
                if primitive in sentences:
                    assumptions.append(primitive)
                not_primitive = Formula('~', primitive)
                if not_primitive in sentences:
                    assumptions.append(not_primitive)
            prover = Prover(assumptions)
            steps_set = set()
            for assumption in assumptions:
                steps_set.add(prover.add_assumption(assumption))
            prover.add_tautological_implication(Formula('&', unsatisfied, Formula('~', unsatisfied)), steps_set)
            return prover.qed()
    return model

def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~first_order_logic.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4
    affirmed_assumption = affirmed_assumption.formula
    negated_assumption = negated_assumption.formula
    proof_true = proof_by_way_of_contradiction(proof_from_affirmation, affirmed_assumption)
    proof_false = proof_by_way_of_contradiction(proof_from_negation, negated_assumption)
    prover = Prover(common_assumptions)
    step_1 = prover.add_proof(proof_true.conclusion, proof_true)
    step_2 = prover.add_proof(proof_false.conclusion, proof_false)
    prover.add_tautological_implication(Formula('&', affirmed_assumption, negated_assumption), {step_1, step_2})
    return prover.qed()

def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~first_order_logic.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5
    proof = proof_by_way_of_contradiction(proof, instantiation)
    prover = Prover(proof.assumptions)
    step_1 = prover.add_assumption(universal)
    step_2 = prover.add_universal_instantiation(instantiation, step_1, constant)
    step_3 = prover.add_proof(proof.conclusion, proof)
    prover.add_tautological_implication(Formula('&', instantiation, Formula('~', instantiation)), {step_2, step_3})
    return prover.qed()

def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    new_sentences = set(sentences)
    const_set = get_constants(sentences)
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6
        if sentence.root == 'A':
            for c in const_set:
                new_sentences.add(
                    sentence.predicate.substitute({sentence.variable: Term(c)}))
    return new_sentences

def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: a valid proof.
        constant: a constant name that does not appear as a template constant
            name in any of the assumptions of the given proof.
        variable: a variable name that does not appear anywhere in given the
            proof or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1
    new_assumptions = set()
    for assumption in proof.assumptions:
        new_assumptions.add(
            Schema(assumption.formula.substitute({constant: Term(variable)}),
                   assumption.templates))
    prover = Prover(new_assumptions)
    for line in proof.lines:
        new_formula = line.formula.substitute({constant: Term(variable)})
        if isinstance(line, Proof.AssumptionLine):
            instantiation_map = dict(line.instantiation_map)
            for k in instantiation_map.keys():
                if not type(instantiation_map[k]) is str:
                    instantiation_map[k] = \
                        instantiation_map[k].substitute({constant: Term(variable)})
            schema = \
                Schema(line.assumption.formula.substitute(
                    {constant: Term(variable)}), line.assumption.templates)
            new_line = Proof.AssumptionLine(new_formula, schema, instantiation_map)
        elif isinstance(line, Proof.UGLine):
            new_line = Proof.UGLine(new_formula, line.predicate_line_number)
        elif isinstance(line, Proof.MPLine):
            new_line = Proof.MPLine(new_formula, line.antecedent_line_number, line.conditional_line_number)
        else:
            new_line = Proof.TautologyLine(new_formula)
        prover._add_line(new_line)
    return prover.qed()

def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~first_order_logic.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2
    variable = 'x'
    proof = replace_constant(proof, constant)
    proof = proof_by_way_of_contradiction(proof, witness.substitute({constant: Term('zz')}))
    witness = witness.substitute({constant: Term(variable)})
    not_witness = Formula('~', witness)
    all_not_witness = Formula('A', variable, not_witness)
    not_all_not_witness = Formula('~', all_not_witness)
    not_existential = Formula('~', existential)
    contradiction = Formula('&', existential, not_existential)

    prover1 = Prover({Schema(existential)})
    step1 = prover1.add_instantiated_assumption(
        Formula('->', all_not_witness, not_witness), prover1.UI,
        {'x': variable, 'c': variable, 'R': not_witness.substitute({variable: Term('_')})})
    step2 = prover1.add_tautological_implication(
        Formula('->', witness, not_all_not_witness), {step1})
    step3 = prover1.add_assumption(existential)
    prover1.add_existential_derivation(not_all_not_witness, step3, step2)
    proof2 = remove_assumption(prover1.qed(), existential)

    prover = Prover(proof.assumptions, True)
    step_1a = prover.add_proof(proof.conclusion, proof)
    print(len(proof.lines))
    step_1b = prover.add_ug(Formula('A', 'zz', proof.conclusion), step_1a)
    step_1 = prover.add_universal_instantiation(not_witness, step_1b, 'x')
    step_2 = prover.add_ug(all_not_witness, step_1)
    print(len(prover._lines)-len(proof.lines))
    step_3 = prover.add_proof(proof2.conclusion, proof2)
    print(len(proof2.lines))
    step_4 = prover.add_tautological_implication(
        Formula('->', all_not_witness, not_existential), {step_3})
    step_5 = prover.add_mp(not_existential, step_2, step_4)
    step_6 = prover.add_assumption(existential)
    prover.add_tautological_implication(contradiction, {step_5, step_6})

    return prover.qed()

def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8
    if is_existentially_closed(sentences):
        return sentences
    new_sentences = set(sentences)
    const_set = get_constants(sentences)
    for sentence in sentences:
        if is_quantifier(sentence.root) and sentence.root == 'E':
            i = 0
            for c in const_set:
                if sentence.predicate.substitute({sentence.variable: Term(c)}) in \
                        sentences:
                    break
                else:
                    i += 1
            if i == len(const_set):
                new_sentences.add(sentence.predicate.substitute(
                    {sentence.variable: Term(next(fresh_constant_name_generator))}))
    return new_sentences
