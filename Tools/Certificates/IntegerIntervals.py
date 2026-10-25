"""Untrusted integer witnesses for the proved IntegerProgram checker.

No floating point, proof terms, or mathematical acceptance reports are emitted.
Real-function identities and validated flow remain separate Lean obligations.
"""
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Bounds:
    """
    Closed integer interval [lo, hi] representing real values after division by a shared scale.
    The constructor rejects reversed endpoints; Lean independently checks every proposed
    enclosure.
    """
    lo: int
    hi: int

    def __post_init__(self):
        """
        Reject noninteger or reversed endpoints before constructing an arithmetic proposal.
        """
        if type(self.lo) is not int or type(self.hi) is not int or self.lo > self.hi:
            raise ValueError("Invalid integer interval")


def ceil_div(n, d):
    """
    Round n/d upward for positive d using integer division, including negative n. This is the
    upper endpoint rule in outward rounding.
    """
    if d <= 0:
        raise ValueError("Nonpositive denominator")
    return -((-n) // d)


class Program:
    """
    A shared arithmetic DAG for the Lean IntegerProgram checker. Negative indices denote
    inputs, nonnegative indices earlier nodes; repeated operations are interned. It proposes
    witnesses and never certifies a real-function identity.
    """
    def __init__(self, bits, inputs=()):
        """
        Choose scale 2**bits, validate the permitted precision, and initialize input intervals
        and the shared operation graph.
        """
        if type(bits) is not int or not 16 <= bits <= 256:
            raise ValueError("Precision must be between 16 and 256 bits")
        self.bits, self.scale = bits, 1 << bits
        self.inputs = list(inputs)
        self.nodes = []
        self.interned = {}

    def interval(self, i):
        """
        Read an input or previously emitted node enclosure. Input index -i-1 addresses input i;
        ordinary indices address DAG nodes.
        """
        return self.inputs[-i - 1] if i < 0 else self.nodes[i][1]

    def node(self, op, args, result):
        """
        Intern an operation with its operands and proposed output. Reusing a node reduces
        witness size without changing the checker obligations.
        """
        key = (op, tuple(args))
        if key in self.interned:
            return self.interned[key]
        index = len(self.nodes)
        self.nodes.append(((op, tuple(args)), result))
        self.interned[key] = index
        return index

    def sub(self, a, b):
        """
        Encode subtraction using addition and negation, the primitive operations accepted by
        Lean.
        """
        return self.add(a, self.neg(b))

    def power(self, a, n):
        """
        Construct a nonnegative integer power by repeated squaring, sharing intermediate nodes
        to keep the emitted graph short.
        """
        if n == 0:
            return self.literal(1)
        if n == 1:
            return a
        half = self.power(a, n // 2)
        square = self.mul(half, half)
        return self.mul(square, a) if n % 2 else square

    def lean_ops(self):
        """
        Serialize operations in the checker's reverse-offset addressing convention. Input
        offsets remain negative in the proposal graph and become back-references relative to
        each emitted operation.
        """
        result = []
        for j, ((op, args), _) in enumerate(self.nodes):
            operands = (f"({args[0]}) {args[1]}" if op == "literal" else
                        " ".join(str(j-i-1) for i in args))
            result.append(f".{op} {operands}")
        return "[" + ",".join(result) + "]"


def outward(value_lo, value_hi, scale):
    """
    Convert rational endpoint bounds to a scale-denominated integer enclosure. Floor the lower
    endpoint and ceil the upper one so rounding can only widen the proposed interval.
    """
    lo, hi = Fraction(value_lo) * scale, Fraction(value_hi) * scale
    return Bounds(lo.numerator // lo.denominator, ceil_div(hi.numerator, hi.denominator))
