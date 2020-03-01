# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: first_order_logic/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from first_order_logic.syntax import *
from first_order_logic.proofs import *
from first_order_logic.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~first_order_logic.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1
    assumptions = list(proof.assumptions)
    assumptions.remove(Schema(assumption))
    prover = Prover(assumptions)
    lines_map = dict()
    for idx, line in enumerate(proof.lines):
        new_formula = Formula('->', assumption, line.formula)
        if isinstance(line, Proof.TautologyLine):
            step = prover.add_tautology(new_formula)
        elif isinstance(line, Proof.MPLine):
            ant = lines_map[line.antecedent_line_number]
            con = lines_map[line.conditional_line_number]
            step = prover.add_tautological_implication(new_formula, {ant, con})
        elif isinstance(line, Proof.UGLine):
            formula = proof.lines[line.predicate_line_number].formula
            unquant = Formula('->', assumption, formula)
            unquant_line = lines_map[line.predicate_line_number]
            var = line.formula.variable
            step_1 = prover.add_ug(Formula('A', var, unquant), unquant_line)
            step_2 = prover.add_instantiated_assumption(Formula('->', Formula('A', var, unquant), new_formula), Prover.US,
                                                        {'x': var, 'R': formula.substitute({var: Term('_')}),
                                                         'Q': assumption})
            step = prover.add_mp(new_formula, step_1, step_2)
        else:
            if line.formula == assumption:
                step = prover.add_tautology(new_formula)
            else:
                step_1 = prover._add_line(line)
                step = prover.add_tautological_implication(new_formula, {step_1})
        lines_map[idx] = step
    return prover.qed()

def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~first_order_logic.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
    new_proof = remove_assumption(proof, assumption)
    prover = Prover(new_proof.assumptions,
                    print_as_proof_forms)
    step_1 = prover.add_proof(new_proof.conclusion, new_proof)
    prover.add_tautological_implication(Formula('~', assumption), {step_1})
    return prover.qed()
