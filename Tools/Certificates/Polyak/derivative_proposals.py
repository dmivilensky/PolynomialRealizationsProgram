"""Exact rational forward-AD proposals for independently checked literal boxes.

Only polynomial coefficient records from the configured archive are evaluated.
The same finite Horner ordering as the consumer expression templates is used;
every resulting interval is separately checked against Lean's AD evaluator.
"""
from fractions import Fraction
from .Payload import group


class RationalInterval:
    def __init__(self, lo, hi=None):
        self.lo = Fraction(lo)
        self.hi = self.lo if hi is None else Fraction(hi)

    def __add__(self, other):
        return RationalInterval(self.lo+other.lo, self.hi+other.hi)

    def __mul__(self, other):
        products = [self.lo*other.lo, self.lo*other.hi,
                    self.hi*other.lo, self.hi*other.hi]
        return RationalInterval(min(products), max(products))


class DualInterval:
    def __init__(self, value, derivative=None):
        self.value = value
        self.derivative = derivative or [RationalInterval(0) for _ in range(8)]

    def __add__(self, other):
        return DualInterval(self.value+other.value,
                            [a+b for a, b in zip(self.derivative, other.derivative)])

    def __mul__(self, other):
        return DualInterval(self.value*other.value,
                            [a*other.value+self.value*b
                             for a, b in zip(self.derivative, other.derivative)])


def _horner(terms, environment, variable=0):
    if not terms:
        return DualInterval(RationalInterval(0))
    if variable == 8:
        return DualInterval(RationalInterval(sum(Fraction(c) for c, _ in terms)))
    groups = {}
    for coefficient, exponents in terms:
        groups.setdefault(exponents[variable], []).append((coefficient, exponents))
    powers = sorted(groups, reverse=True)
    value = _horner(groups[powers[0]], environment, variable+1)
    previous = powers[0]
    for power in powers[1:]:
        for _ in range(previous-power):
            value = environment[variable]*value
        value = _horner(groups[power], environment, variable+1)+value
        previous = power
    for _ in range(previous):
        value = environment[variable]*value
    return value


def _rounded(interval):
    scale = 10**12
    lower = interval.lo.numerator*scale // interval.lo.denominator-2
    upper = -((-interval.hi.numerator*scale) // interval.hi.denominator)+2
    return Fraction(lower, scale), Fraction(upper, scale)


def central_derivative_boxes(record):
    intervals = [RationalInterval(*record['parameter'])]
    intervals += [RationalInterval(Fraction(c)-Fraction(r), Fraction(c)+Fraction(r))
                  for c, r in zip(record['centre'], record['radii'])]
    environment = []
    for index, interval in enumerate(intervals):
        derivative = [RationalInterval(0) for _ in range(8)]
        derivative[index] = RationalInterval(1)
        environment.append(DualInterval(interval, derivative))
    source = group('p5')['polynomials']
    expected = ['h', 'A', 'B', 'y', 'P', 'D', 'w2', 'w3']
    for index in range(7):
        if source[f'F{index}']['variables'] != expected:
            raise ValueError('unexpected central derivative polynomial variables')
    rows = [_horner(source[f'F{i}']['terms'], environment).derivative
            for i in range(7)]
    return [[_rounded(entry) for entry in row[1:]] for row in rows], [
        _rounded(row[0]) for row in rows]
