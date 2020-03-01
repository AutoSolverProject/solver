# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositional_logic/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositional_logic.syntax import *
from propositional_logic.proofs import *
from propositional_logic.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositional_logic.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a

    con_line = len(antecedent_proof.lines) - 1
    return Proof(InferenceRule(antecedent_proof.statement.assumptions, consequent),
                 antecedent_proof.rules.union({MP, conditional}),
                 list(antecedent_proof.lines) +
                 [Proof.Line(Formula('->', antecedent_proof.statement.conclusion, consequent), conditional, []),
                  Proof.Line(consequent, MP, [con_line, con_line + 1])])

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositional_logic.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b

    con1_line = len(antecedent1_proof.lines) - 1
    con2_line = con1_line + len(antecedent2_proof.lines)
    new_statement = InferenceRule(antecedent1_proof.statement.assumptions, consequent)
    new_rules = antecedent1_proof.rules.union({MP, double_conditional})
    new_lines = list(antecedent1_proof.lines)
    num_lines = len(new_lines)
    for line in list(antecedent2_proof.lines):
        if line.is_assumption():
            new_lines.append(line)
        else:
            new_assumptions = list()
            for assumption in line.assumptions:
                new_assumptions.append(assumption + num_lines)
            new_lines.append(Proof.Line(line.formula, line.rule, new_assumptions))
    new_lines.append(Proof.Line(Formula('->', antecedent1_proof.statement.conclusion,
                                        Formula('->', antecedent2_proof.statement.conclusion, consequent)),
                                double_conditional, []))
    new_lines.append(Proof.Line(Formula('->', antecedent2_proof.statement.conclusion, consequent),
                             MP, [con1_line, len(new_lines) - 1]))
    new_lines.append(Proof.Line(consequent, MP, [con2_line, len(new_lines) - 1]))
    return Proof(new_statement, new_rules, new_lines)


def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositional_logic.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`, and
        `~propositional_logic.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    assumption = proof.statement.assumptions[-1]
    new_statement = InferenceRule(proof.statement.assumptions[:-1], Formula('->', assumption, proof.statement.conclusion))
    new_rules = set(proof.rules).union({MP, I0, I1, D})
    new_lines = list()
    new_line_dict = dict()
    for line in range(len(proof.lines)):
        formula = proof.lines[line].formula
        if proof.lines[line].is_assumption():
            if formula == assumption:
                new_lines.append(Proof.Line(Formula('->', assumption, assumption), I0, []))
                last_line_idx = len(new_lines) - 1
            else:
                new_lines.append(proof.lines[line])
                antecedent_line = len(new_lines) - 1
                new_lines.append(Proof.Line(Formula('->', formula, Formula('->', assumption, formula)), I1, []))
                conditional_line = len(new_lines) - 1
                new_lines.append(Proof.Line(Formula('->', assumption, formula), MP, [antecedent_line, conditional_line]))
                last_line_idx = len(new_lines) - 1
        else:
            if len(proof.lines[line].assumptions) == 0:
                new_lines.append(proof.lines[line])
                antecedent_line = len(new_lines) - 1
                assumption_implies_formula = Formula('->', assumption, formula)
                new_lines.append(Proof.Line(Formula('->', formula, assumption_implies_formula), I1, []))
                conditional_line = len(new_lines) - 1
                new_lines.append(Proof.Line(assumption_implies_formula, MP, [antecedent_line, conditional_line]))
                last_line_idx = len(new_lines) - 1
            else:
                antecedent_line = proof.lines[line].assumptions[0]
                conditional_line = proof.lines[line].assumptions[1]
                antecedent = proof.lines[antecedent_line].formula
                antecedent = Formula('->', assumption, antecedent)
                antecedent_line = new_line_dict[antecedent_line]
                conditional = proof.lines[conditional_line].formula
                conditional = Formula('->', assumption, conditional)
                conditional_line = new_line_dict[conditional_line]
                consequent = Formula('->', assumption, formula)
                conditional_implies_antecedent_implies_consequent = \
                    Formula('->', conditional, Formula('->', antecedent, consequent))
                new_lines.append(Proof.Line(conditional_implies_antecedent_implies_consequent, D, []))
                last_line = len(new_lines) - 1
                new_lines.append(
                    Proof.Line(conditional_implies_antecedent_implies_consequent.second, MP, [conditional_line, last_line]))
                last_line = len(new_lines) - 1
                new_lines.append(Proof.Line(consequent, MP, [antecedent_line, last_line]))
                last_line_idx = len(new_lines) - 1
        new_line_dict[line] = last_line_idx
    return Proof(new_statement, new_rules, new_lines)

def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositional_logic.axiomatic_systems.MP` and
        `~propositional_logic.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6

    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)

def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositional_logic.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7

    formula = proof.statement.assumptions[-1].first
    p_implies_p = proof.statement.conclusion.first
    proof = remove_assumption(proof)
    lines = list(proof.lines)
    last_line = len(lines) - 1
    lines.append(Proof.Line(Formula('->', proof.lines[-1].formula, Formula('->', p_implies_p, formula)), N, []))
    lines.append(Proof.Line(Formula('->', p_implies_p, formula), MP, [last_line, last_line + 1]))
    last_line = len(lines) - 1
    lines.append(Proof.Line(p_implies_p, I0, []))
    lines.append(Proof.Line(formula, MP, [last_line + 1, last_line]))
    return Proof(InferenceRule(proof.statement.assumptions, formula), set(proof.rules).union({MP, I0, I1, D, N}), lines)
