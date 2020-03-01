# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositional_logic/syntax.py

"""Syntactic handling of propositional formulae."""

from __future__ import annotations
#from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen

def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == 'T' or s == 'F'

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}

@frozen
class Formula:
    """An immutable propositional formula in tree representation.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        root = self.root
        if is_constant(root) or is_variable(root):
            return root
        elif is_unary(root):
            return root + repr(self.first)
        elif is_binary(root):
            return "(" + repr(self.first) + root + repr(self.second) + ")"

    def variables(self) -> Set[str]:
        """Finds all atomic propositional_logic (variables) in the current formula.

        Returns:
            A set of all atomic propositional_logic used in the current formula.
        """
        # Task 1.2
        variables = set()
        root = self.root
        if is_variable(root):
            variables.add(root)
        elif is_unary(root) or is_binary(root):
            variables = variables.union(self.first.variables())
            if is_binary(root):
                variables = variables.union(self.second.variables())
        return variables


    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3

        operators = set()
        root = self.root
        if is_constant(root):
            operators.add(root)
        elif is_unary(root) or is_binary(root):
            operators = operators.union(self.first.operators())
            if is_binary(root):
                operators = operators.union(self.second.operators())
            operators.add(root)
        return operators

        
    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        # Task 1.4

        if len(s) == 0:
            return None, "Can't parse Formula from empty string."
        if is_constant(s[0]) or (is_variable(s[0]) and (len(s) == 1 or not s[1].isdigit())):
            return Formula(s[0]), s[1:] if len(s) > 1 else ''
        elif is_variable(s[0]):
            i = 1
            while i < len(s) and s[i].isdigit():
                i += 1
            return Formula(s[:i]), s[i:] if len(s) > 1 else ''
        elif is_unary(s[0]):
            f, r = Formula.parse_prefix(s[1:])
            if f is None:
                return f, "Can't parse Formula from any prefix of:" + s
            return Formula('~', f), r
        elif s[0] == '(':
            f1, r1 = Formula.parse_prefix(s[1:])
            if f1 is None or len(r1) == 0 or not (is_binary(r1[0]) or is_binary(r1[:2]) or is_binary(r1[:3])):
                return None, "Can't parse Formula from any prefix of:" + s
            if is_binary(r1[0]):
                op = r1[0]
            elif is_binary(r1[:2]):
                op = r1[:2]
            else:
                op = r1[:3]
            f2, r2 = Formula.parse_prefix(r1[len(op):])
            if f2 is None or len(r2) == 0 or r2[0] != ')':
                return None, "Can't parse Formula from any prefix of:" + s
            return Formula(op, f1, f2), r2[1:] if len(r2) > 0 else ''
        return None, "Can't parse Formula from any prefix of:" + s




    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5

        f, r = Formula.parse_prefix(s)
        return f is not None and r == ''
        
    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s)
        # Task 1.6
        return Formula.parse_prefix(s)[0]

# Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

        root = self.root
        if is_variable(root) or is_constant(root):
            return root
        elif is_unary(root):
            return '~' + self.first.polish()
        else:
            return root + self.first.polish() + self.second.polish()

    @staticmethod
    def parse_polish(s: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

        if is_variable(s[0]) or is_constant(s[0]):
            return Formula(s)
        elif is_unary(s[0]):
            return Formula(s[0], Formula.parse_polish(s[1:]))
        else:
            root = s[0]
            if root == '-':
                root += s[1]
            next_idx = len(root)
            next = s[next_idx]
            if is_constant(next):
                return Formula(root, Formula(next), Formula.parse_polish(s[next_idx + 1:]))
            elif is_variable(next):
                i = next_idx + 1
                while i < len(s):
                    if not s[i].isdigit():
                        return Formula(root, Formula(s[next_idx: i]), Formula.parse_polish(s[i:]))
                    i += 1
            elif is_unary(next):
                i = next_idx + 1
                while not (is_constant(s[i]) or is_variable(s[i])):
                    i += 1
                if is_variable(s[i]):
                    i += 1
                    while s[i].isdigit():
                        i += 1
                return Formula(root, Formula.parse_polish(s[next_idx: i]), Formula.parse_polish(s[i:]))
            else:
                num_ops = 2
                i = next_idx + 1
                while num_ops != 0:
                    if s[i] == '>' or is_unary(s[i]):
                        i += 1
                    elif is_binary(s[i]) or s[i] == '-':
                        num_ops += 2
                    elif is_constant(s[i]):
                        num_ops -= 1
                        i += 1
                    else:
                        num_ops -= 1
                        i += 1
                        while s[i].isdigit():
                            i += 1
                return Formula(root, Formula.parse_polish(s[next_idx: i]), Formula.parse_polish(s[i:]))


# Tasks for Chapter 3

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

        formula = self
        root = self.root
        if is_variable(root) and root in substitution_map.keys():
            formula = substitution_map[root]
        elif is_unary(root) or is_binary(root):
            first = self.first.substitute_variables(substitution_map)
            if is_unary(root):
                formula = Formula('~', first)
            else:
                second = self.second.substitute_variables(substitution_map)
                formula = Formula(root, first, second)
        return  formula


    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4

        formula = self
        root = self.root
        var_sub_map = dict()

        if is_constant(root) and root in substitution_map.keys():
            formula = substitution_map[root]
        elif is_unary(root) or is_binary(root):
            first = self.first.substitute_operators(substitution_map)
            if is_unary(root):
                formula = Formula(root, first)
            var_sub_map['p'] = first
            if is_binary(root):
                second = self.second.substitute_operators(substitution_map)
                var_sub_map['q'] = second
                formula = Formula(root, first, second)
            if root in substitution_map.keys():
                formula = substitution_map[root].substitute_variables(var_sub_map)
        return formula

