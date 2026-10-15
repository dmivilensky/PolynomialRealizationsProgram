"""Untrusted local polynomial witnesses, retaining all residual cancellation.

The arithmetic mirrors IntegerPolynomial. This module does not accept any
mathematical claim; acceptance requires the Lean source and flow bridges.
"""
from fractions import Fraction as F
from IntegerIntervals import Bounds, Program, outward, ceil_div
from ReferenceJets import reference_source, I


class Polynomials:
    """
    Scaled integer coefficient enclosures on the normalized cell coordinate [0,1]. Arithmetic
    mirrors IntegerPolynomial; truncation and residual acceptance are checked separately in
    Lean.
    """
    def __init__(self, bits):
        """
        Set the common coefficient denominator to 2**bits.
        """
        self.bits, self.s = bits, 1 << bits

    def literal(self, q):
        """
        Emit an outward-rounded constant polynomial.
        """
        return [outward(q, q, self.s)]

    def add(self, a, b):
        """
        Add coefficient bounds, padding the shorter polynomial with exact zero.
        """
        z = Bounds(0, 0)
        return [Bounds((a[i] if i < len(a) else z).lo +
                       (b[i] if i < len(b) else z).lo,
                       (a[i] if i < len(a) else z).hi +
                       (b[i] if i < len(b) else z).hi)
                for i in range(max(len(a), len(b)))]

    def neg(self, a):
        """
        Negate all coefficient intervals with reversed endpoints.
        """
        return [Bounds(-v.hi, -v.lo) for v in a]

    def sub(self, a, b):
        """
        Subtract coefficient enclosures through negation and addition.
        """
        return self.add(a, self.neg(b))

    def mul_b(self, a, b):
        """
        Multiply two scale-denominated interval coefficients and round outward after rescaling.
        """
        v = [x*y for x in (a.lo, a.hi) for y in (b.lo, b.hi)]
        return Bounds(min(v)//self.s, ceil_div(max(v), self.s))

    def mul(self, a, b):
        """
        Convolve coefficient intervals using a Horner-style accumulation. Delay scale division
        until each full coefficient sum has been accumulated.
        """
        out = []
        for v in reversed(a):
            products=[]
            for w in b:
                xs=[x*y for x in (v.lo,v.hi) for y in (w.lo,w.hi)]
                products.append(Bounds(min(xs),max(xs)))
            out=self.add(products,[Bounds(0,0)]+out)
        return [Bounds(v.lo//self.s,ceil_div(v.hi,self.s)) for v in out]

    def power(self, a, n):
        """
        Construct a nonnegative polynomial power by repeated squaring.
        """
        if n == 0:
            return self.literal(1)
        half = self.power(a, n//2)
        sq = self.mul(half, half)
        return self.mul(sq, a) if n % 2 else sq

    def factor(self, q, a):
        """
        Multiply a polynomial by an outward-rounded rational constant.
        """
        return self.mul(self.literal(q), a)

    def range(self, a):
        """
        Enclose a polynomial on [0,1] by interval Horner evaluation. This supplies the tail
        bound needed for sound degree truncation.
        """
        out = Bounds(0, 0)
        for v in reversed(a):
            prod = self.mul_b(Bounds(0, self.s), out)
            out = Bounds(v.lo + prod.lo, v.hi + prod.hi)
        return out

    def midpoint(self, qs):
        """
        Choose dyadic point coefficients near rational proposals. They are candidate data, not
        interval enclosures of unknown exact coefficients.
        """
        return [Bounds(round(F(q)*self.s), round(F(q)*self.s)) for q in qs]


class PolynomialProgram(Program):
    """
    An arithmetic DAG whose node witnesses are truncated polynomial enclosures. Multiplication
    folds the discarded tail into the constant coefficient; Lean verifies this truncation rule.
    """
    def __init__(self, bits, inputs, cap=13):
        """
        Initialize shared DAG inputs, fixed scale and the retained coefficient cap.
        """
        super().__init__(bits, inputs)
        self.cap=cap
        self.polys = Polynomials(bits)

    def literal(self, q):
        """
        Register a rational literal with its constant-polynomial enclosure.
        """
        q = F(q)
        return self.node('literal', (q.numerator,q.denominator), self.polys.literal(q))

    def add(self, a, b):
        """
        Register coefficientwise polynomial addition.
        """
        return self.node('add',(a,b),self.polys.add(self.interval(a),self.interval(b)))

    def neg(self, a):
        """
        Register coefficientwise polynomial negation.
        """
        return self.node('neg',(a,),self.polys.neg(self.interval(a)))

    def mul(self, a, b):
        """
        Multiply and trim exact trailing zeros. If the coefficient cap is exceeded, enclose the
        discarded tail on [0,1] and widen the retained constant coefficient.
        """
        out=self.polys.mul(self.interval(a),self.interval(b))
        while out and out[-1]==Bounds(0,0):out.pop()
        if len(out)>self.cap:
            tail=self.polys.range(out[self.cap:])
            rest=self.polys.mul_b(Bounds(0,self.scale),tail)
            out=self.polys.add([rest],out[:self.cap])
        return self.node('mul',(a,b),out)

    def inv(self, a):
        """
        Reject inverse operations: this residual program must remain polynomial so that
        cancellation survives interval evaluation.
        """
        raise ValueError('Nonpolynomial operation')


def residual_program(ref, inputs, bits, cap=13):
    """
    Build the polynomial expression for the actual reference ODE residual in the fixed input
    layout. Keeping the expression polynomial preserves cancellations before its range is
    bounded.
    """
    P = PolynomialProgram(bits, inputs, cap)
    t, pi, z, p, pd = -1,-2,-3,-4,-5
    h = P.sub(P.literal(2),P.power(t,3))
    Q = P.mul(P.power(t,3),h)
    k = P.mul(P.literal(F(1,4)),P.power(pi,2))
    den,pn = P.literal(1),P.literal(ref[5])
    for j in range(5):
        di = P.add(Q,P.literal(ref[7+2*j]))
        pn = P.add(P.mul(pn,di),P.mul(P.literal(ref[6+2*j]),P.mul(Q,den)))
        den = P.mul(den,di)
    root = P.sub(P.mul(P.sub(P.mul(k,P.power(z,3)),
                              P.mul(P.literal(3),P.mul(P.mul(t,h),z))),den),
                 P.mul(P.literal(2),P.mul(h,pn)))
    factor = P.mul(k,P.sub(P.mul(P.literal(3),P.power(t,2)),pd))
    ode = P.sub(P.sub(P.add(P.mul(factor,P.power(z,2)),P.mul(pd,P.mul(t,h))),
                      P.mul(P.literal(6),p)),P.mul(P.literal(3*ref[1]),P.power(p,2)))
    return P,dict(k=k,den=den,root=root,factor=factor,ode=ode)


def residual_polynomials(ref, a, b, saved, bits=144, degree=12):
    """
    Return exact dyadic approximants and interval polynomial residuals.
    """
    P = Polynomials(bits)
    reflected = a >= 1
    t0, dt = (2-a, a-b) if reflected else (a, b-a)
    t = [outward(t0, t0, P.s), outward(dt, dt, P.s)]
    w, _ = reference_source(ref, I.point(t0), degree, ref[1])
    z = P.midpoint((v.lo+v.hi)/2 * dt**j for j, v in enumerate(w[6]))
    p = P.midpoint((u+v)/2*(b-a)**j for j, (u,v) in enumerate(saved))
    pd = P.midpoint(F(v.lo, P.s)*j/(b-a) for j,v in enumerate(p) if j)
    return dict(p=p,pd=pd,z=z,t=t,z_range=P.range(z),p_range=P.range(p))
