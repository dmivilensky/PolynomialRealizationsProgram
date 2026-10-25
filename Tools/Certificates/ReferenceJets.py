"""Untrusted rational proposals for compact root residual polynomials.

No result of this module is mathematical evidence. Only the separately checked polynomial residual is mathematical evidence.
"""
from dataclasses import dataclass
from fractions import Fraction as F

PRECISION = 192
UNIT = 1 << PRECISION


@dataclass(frozen=True)
class I:
    """
    Rational interval arithmetic for untrusted Taylor-coefficient proposals. Rounding uses a
    192-bit dyadic grid; the Lean residual checker remains responsible for soundness.
    """
    lo: F
    hi: F

    def __post_init__(self):
        """
        Coerce both endpoints to exact fractions and reject a reversed interval.
        """
        object.__setattr__(self, "lo", F(self.lo))
        object.__setattr__(self, "hi", F(self.hi))
        if self.lo > self.hi:
            raise ValueError("Reversed interval")

    @staticmethod
    def point(q):
        """
        Embed an exact rational as a degenerate interval.
        """
        return I(q, q)

    def __add__(self, b):
        """
        Add endpoint bounds without rounding; callers round accumulated results explicitly.
        """
        return I(self.lo+b.lo, self.hi+b.hi)

    def __neg__(self):
        """
        Negate an interval, reversing and negating its endpoints.
        """
        return I(-self.hi, -self.lo)

    def __sub__(self, b):
        """
        Subtract through interval addition and negation.
        """
        return self+-b

    def __mul__(self, b):
        """
        Enclose interval products using the minimum and maximum of all four endpoint products.
        """
        xs = [a*c for a in (self.lo, self.hi) for c in (b.lo, b.hi)]
        return I(min(xs), max(xs))

    def inv(self):
        """
        Invert an interval that excludes zero. The reciprocal reverses endpoint order;
        intervals containing zero are rejected.
        """
        if self.lo <= 0 <= self.hi:
            raise ValueError("Reciprocal interval contains zero")
        return I(1/self.hi, 1/self.lo)

    def rounded(self):
        """
        Widen endpoints to the fixed 192-bit dyadic grid, flooring the lower endpoint and
        ceiling the upper.
        """
        l, u = self.lo*UNIT, self.hi*UNIT
        return I(F(l.numerator//l.denominator, UNIT),
                 F(-((-u.numerator)//u.denominator), UNIT))

    def subset(self, b):
        """
        Test closed-interval containment; used to check proposal refinement.
        """
        return b.lo <= self.lo and self.hi <= b.hi

    def power(self, n):
        """
        Build a nonnegative power by recursive interval multiplication and outward rounding.
        The exponent-zero interval is exactly one.
        """
        if n == 0:
            return I.point(1)
        return (self*self.power(n-1)).rounded()

    def square(self):
        """
        Enclose a square using endpoint signs, including zero when the input straddles it. This
        avoids treating the two occurrences of the same variable as independent.
        """
        if 0 <= self.lo:
            return I(self.lo**2, self.hi**2).rounded()
        if self.hi <= 0:
            return I(self.hi**2, self.lo**2).rounded()
        return I(0, max(self.lo**2, self.hi**2)).rounded()


ZERO = I.point(0)


def isum(xs):
    """
    Accumulate interval terms with outward rounding at each addition, controlling fraction
    growth.
    """
    result = ZERO
    for x in xs:
        result = (result+x).rounded()
    return result


def constant(q, n):
    """
    Create a degree-n Taylor jet of a constant: its zeroth coefficient is q and its remaining
    coefficients vanish.
    """
    return [I.point(q)]+[ZERO]*n


def variable(x, n):
    """
    Create the Taylor jet for the local coordinate: its constant term is x and its first
    derivative coefficient is one.
    """
    return [x]+([I.point(1)]+[ZERO]*(n-1) if n else [])


def add(a, b):
    """
    Add corresponding jet coefficients with outward rounding. Input jets have the same fixed
    degree.
    """
    return [(x+y).rounded() for x, y in zip(a, b)]


def neg(a):
    """
    Negate all Taylor coefficients.
    """
    return [-x for x in a]


def convolution(a, b, j):
    """
    Compute coefficient j of a product using the finite Cauchy convolution.
    """
    return isum((a[i]*b[j-i]).rounded() for i in range(j+1))


def square_convolution(a, j):
    """
    Compute coefficient j of a square, using the dedicated square enclosure on diagonal
    products.
    """
    return isum(a[i].square() if i == j-i else (a[i]*a[j-i]).rounded()
                for i in range(j+1))


def square(a):
    """
    Build the truncated square jet coefficient by coefficient.
    """
    return [square_convolution(a, j) for j in range(len(a))]


def mul(a, b):
    """
    Build the truncated product jet by Cauchy convolution through the input degree.
    """
    return [convolution(a, b, j) for j in range(len(a))]


def reciprocal(a):
    """
    Solve a*result=1 coefficient by coefficient. The zeroth coefficient must exclude zero; each
    higher coefficient uses only earlier reciprocal coefficients.
    """
    n = len(a)-1
    result = [a[0].inv()]+[ZERO]*n
    for j in range(1, n+1):
        result[j] = (-isum((a[i+1]*result[j-i-1]).rounded()
                           for i in range(j))*a[0].inv()).rounded()
    return result


def centered_square(z, n):
    """
    Compute the quadratic convolution involving positive-order root coefficients, separated
    from the zeroth root coefficient in the cubic recurrence.
    """
    return isum(z[i+1].square() if i+1 == n-i else (z[i+1]*z[n-i]).rounded()
                for i in range(n))


def cubic_slope(a, b, z):
    """
    Propose the positive denominator 2*a[0]+3*b[0]/z[0] for implicit differentiation of the
    cubic at its positive root.
    """
    return (I.point(2)*a[0]+I.point(3)*b[0]*z[0].inv().rounded()).rounded()


def cubic_step(a, b, z, n):
    """
    Solve the next coefficient of z**3-a*z-b=0. Separate terms containing the unknown
    coefficient from lower-order convolutions and divide by the proposed cubic slope.
    """
    linear = isum((a[i+1]*z[n-i]).rounded() for i in range(n+1))
    cube = isum((z[i+1]*centered_square(z, n-i-1)).rounded() for i in range(n))
    numerator = (b[n+1]+linear-I.point(3)*z[0]*centered_square(z, n)-cube).rounded()
    return (numerator*cubic_slope(a, b, z).inv().rounded()).rounded()


def root_bracket(a, b):
    """
    Bracket the positive cubic root using exact rational bisection at endpoint parameters.
    Require nonnegative a and positive b, then check endpoint residual signs after rounding.
    """
    if a.lo < 0 or b.lo <= 0:
        raise ValueError("Invalid positive cubic parameters")

    def bracket(av, bv):
        """
        Bisect a scalar cubic between zero and 1+a+b. The sign of the exact cubic residual
        selects which endpoint to replace.
        """
        lo, hi = F(0), F(1)+av+bv
        for _ in range(PRECISION+32):
            m = (lo+hi)/2
            if m**3-av*m-bv <= 0:
                lo = m
            else:
                hi = m
        return lo, hi

    result = I(bracket(a.lo, b.lo)[0], bracket(a.hi, b.hi)[1]).rounded()
    if not (0 < result.lo and result.lo**3-a.lo*result.lo-b.lo <= 0
            and 0 <= result.hi**3-a.hi*result.hi-b.hi):
        raise ValueError("Cubic bracket proposal failed")
    return result


def cubic(a, b):
    """
    Construct a positive-root jet from its bracket and coefficient recurrence. Reject a
    nonpositive slope before any division; these remain proposals for Lean's residual checks.
    """
    n = len(a)-1
    result = [root_bracket(a[0], b[0])]+[ZERO]*n
    if cubic_slope(a, b, result).lo <= 0:
        raise ValueError("Nonpositive cubic slope")
    for j in range(n):
        result[j+1] = cubic_step(a, b, result, j)
    return result


def reference_source(ref, x, n, sigma):
    """
    Match ReferenceJetSource, recording every inverse/root proposal.
    """
    # The accepted input layout is fixed by ReferenceInputs.
    if len(ref) != 19 or ref[0] != 1 or ref[4] != 11 or ref[16] != 2:
        raise ValueError("Unexpected reference layout")
    count = 5
    w = {}
    t = variable(x, n)
    h = add(constant(2, n), neg(mul(square(t), t)))
    q = mul(mul(square(t), t), h)
    terms = []
    for i in range(count):
        w[i] = reciprocal(add(q, constant(ref[7+2*i], n)))
        terms.append(mul(constant(ref[6+2*i], n), mul(q, w[i])))
    total = constant(0, n)
    for term in reversed(terms):
        total = add(term, total)
    p = add(constant(ref[5], n), total)
    w[count+4] = p
    pi = [I(F(314159265358979323846264338327950288419716939937510, 10**50),
            F(314159265358979323846264338327950288419716939937511, 10**50))]+[ZERO]*n
    k = mul(constant(F(1, 4), n), square(pi))
    w[count] = reciprocal(k)
    alpha = mul(constant(3, n), mul(mul(t, h), w[count]))
    beta = mul(constant(2, n), mul(mul(p, h), w[count]))
    w[count+5], w[count+6] = alpha, beta
    w[count+1] = cubic(alpha, beta)
    w[count+2] = reciprocal(w[count+1])
    speed = add(mul(constant(2, n), mul(t, h)),
                mul(constant(2, n), mul(mul(p, h), w[count+2])))
    w[count+7] = speed
    w[count+3] = reciprocal(speed)
    velocity = mul(constant(3, n), w[count+3])
    amplitude = mul(t, w[count+1])
    w[count+8], w[count+9] = velocity, amplitude
    c = mul(mul(velocity, k), square(amplitude))
    a = mul(constant(-2, n), velocity)
    b = mul(constant(-sigma, n), velocity)
    return w, (c, a, b)

