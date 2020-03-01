# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositional_logic/some_proofs.py

"""Some proofs in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                       Formula.parse('(x&y)'))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('x'))

def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE2_RULE`, and
    `AE1_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE2_RULE`, and `AE1_RULE`.
    """
    # Task 4.7

    statement = InferenceRule([Formula.parse('(p&q)')], Formula.parse('(q&p)'))
    rules = {A_RULE, AE1_RULE, AE2_RULE}
    lines = []
    lines.append(Proof.Line(statement.assumptions[0]))
    lines.append(Proof.Line(Formula.parse('q'), AE1_RULE, [0]))
    lines.append(Proof.Line(Formula.parse('p'), AE2_RULE, [0]))
    lines.append(Proof.Line(statement.conclusion, A_RULE, [1, 2]))
    return Proof(statement, rules, lines)

def prove_I0() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.I0` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I1`,
    and `~propositional_logic.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.I0` from no
        assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I1`, and
        `~propositional_logic.axiomatic_systems.D`.
    """
    # Task 4.8

    proof = Proof(InferenceRule([], Formula.parse('(p->p)')),
                  {MP, I1, D},
                  [Proof.Line(Formula.parse('((p->((p->p)->p))->((p->(p->p))->(p->p)))'),
                              D, []),
                   Proof.Line(Formula.parse('(p->((p->p)->p))'),
                              I1, []),
                   Proof.Line(Formula.parse('((p->(p->p))->(p->p))'),
                              MP, [1, 0]),
                   Proof.Line(Formula.parse('(p->(p->p))'),
                              I1, []),
                   Proof.Line(Formula.parse('(p->p)'),
                              MP, [3, 2])])
    return proof

#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositional_logic.axiomatic_systems.MP`,
    `~propositional_logic.axiomatic_systems.I0`, `~propositional_logic.axiomatic_systems.I1`,
    and `~propositional_logic.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`, and
        `~propositional_logic.axiomatic_systems.D`.
    """
    # Task 5.5
    # lines = [Proof.Line(Formula.parse('((q->r)->(p->(q->r)))'), I1, []),
    #          Proof.Line(Formula.parse('(q->r)')),
    #          Proof.Line(Formula.parse('(p->(q->r))'), MP, [1, 0]),
    #          Proof.Line(Formula.parse('((p->(q->r))->((p->q)->(p->r)))'), D, []),
    #          Proof.Line(Formula.parse('((p->q)->(p->r))'), MP, [2, 3]),
    #          Proof.Line(Formula.parse('(p->q)')),
    #          Proof.Line(Formula.parse('(p->r)'), MP, [5, 4])]
    # return Proof(HS, {MP, I0, I1, D}, lines)
    statement = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)'), Formula.parse('p')], Formula.parse('r'))
    rules = {MP, I0, I1, D}
    lines = [Proof.Line(Formula.parse('p')), Proof.Line(Formula.parse('(p->q)')),
             Proof.Line(Formula.parse('q'), MP, [0, 1]), Proof.Line(Formula.parse('(q->r)')),
             Proof.Line(Formula.parse('r'), MP, [2,3])]
    return remove_assumption(Proof(statement, rules, lines))

def prove_I2() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.I2` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    and `~propositional_logic.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.I2` from no
        assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    # Optional Task 6.7a

#: Double-negation elimination
NNE = InferenceRule([], Formula.parse('(~~p->p)'))

def prove_NNE() -> Proof:
    """Proves `NNE` via `~propositional_logic.axiomatic_systems.MP`,
    `~propositional_logic.axiomatic_systems.I0`, `~propositional_logic.axiomatic_systems.I1`,
    `~propositional_logic.axiomatic_systems.D`, and
    `~propositional_logic.axiomatic_systems.N`.

    Returns:
        A valid proof of `NNE` from no assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    # Optional Task 6.7b

def prove_NN() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.NN` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    and `~propositional_logic.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.NN` from no
        assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    # Optional Task 6.7c

#: Contraposition
CP = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))

def prove_CP() -> Proof:
    """Proves `CP` via `~propositional_logic.axiomatic_systems.MP`,
    `~propositional_logic.axiomatic_systems.I0`, `~propositional_logic.axiomatic_systems.I1`,
    `~propositional_logic.axiomatic_systems.D`, and
    `~propositional_logic.axiomatic_systems.N`.

    Returns:
        A valid proof of `CP` from no assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    # Optional Task 6.7d

def prove_NI() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.NI` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    and `~propositional_logic.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.NI` from no
        assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    # Optional Task 6.7e

#: Consequentia mirabilis
CM = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))

def prove_CM() -> Proof:
    """Proves `CM` via `~propositional_logic.axiomatic_systems.MP`,
    `~propositional_logic.axiomatic_systems.I0`, `~propositional_logic.axiomatic_systems.I1`,
    `~propositional_logic.axiomatic_systems.D`, and
    `~propositional_logic.axiomatic_systems.N`.

    Returns:
        A valid proof of `CM` from no assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    # Optional Task 6.7f

def prove_R() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.R` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    and `~propositional_logic.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.R` from no assumptions
        via the inference rules `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N`.
    """
    # Optional Task 6.7g

def prove_N() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.N` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    and `~propositional_logic.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.N` from no assumptions
        via the inference rules `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.N_ALTERNATIVE`.
    """
    # Optional Task 6.8

def prove_NA1() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.NA1` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    `~propositional_logic.axiomatic_systems.N`, and
    `~propositional_logic.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.NA1` from no
        assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.AE1`.
    """
    # Optional Task 6.9a

def prove_NA2() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.NA2` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    `~propositional_logic.axiomatic_systems.N`, and
    `~propositional_logic.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.NA2` from no
        assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.AE2`.
    """
    # Optional Task 6.9b

def prove_NO() -> Proof:
    """Proves `~propositional_logic.axiomatic_systems.NO` via
    `~propositional_logic.axiomatic_systems.MP`, `~propositional_logic.axiomatic_systems.I0`,
    `~propositional_logic.axiomatic_systems.I1`, `~propositional_logic.axiomatic_systems.D`,
    `~propositional_logic.axiomatic_systems.N`, and
    `~propositional_logic.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositional_logic.axiomatic_systems.NO` from no
        assumptions via the inference rules
        `~propositional_logic.axiomatic_systems.MP`,
        `~propositional_logic.axiomatic_systems.I0`,
        `~propositional_logic.axiomatic_systems.I1`,
        `~propositional_logic.axiomatic_systems.D`, and
        `~propositional_logic.axiomatic_systems.OE`.
    """
    # Optional Task 6.9c
