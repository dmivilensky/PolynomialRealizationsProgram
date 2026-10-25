"""Callable exact suite: regimes/extra_signs.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as s, json
from pathlib import Path
from ..algebra.bernstein import certify_positive
from .. import interval as ic
from flint import arb

def run(ctx, independent=True):
    z, c, a = s.symbols('z c a')
    DD = 2 + z * c + z * z * (c * c - 1)
    EE = 1 + z * c + z * z * (2 * c * c - 1)
    for m in range(1, 13):
        for sign in (-1, 1):
            if (m, sign) in ((1, -1), (2, 1), (3, 1)):
                continue
            p = s.cancel(z ** (m - 1) * (z * (1 + z * c) * (s.chebyshevt(m, 1 / z) - s.chebyshevt(m, c)) + sign * DD * s.chebyshevu(m - 1, c) - sign * EE * s.chebyshevu(m - 1, 1 / z)))
            if sign == 1 and m >= 4:
                p = s.cancel(p / z ** 2)
            p = s.expand(p.subs(c, -a * z / 2))
            ok = certify_positive(p, (z, a), [(0, s.Rational(3, 4)), (0, 1)])
            ctx.note('P1 slack', m, sign, ctx.check(ok, 'regimes/extra_signs.py:14: ok'), flush=True)
            ctx.check(ok[0], 'regimes/extra_signs.py:14: ok[0]')
    ctx.check(s.Rational(3, 4) ** (-10) / 4 > 4, 'regimes/extra_signs.py:16: s.Rational(3, 4) ** (-10) / 4 > 4')
    if not independent:
        return
    G, w, v = s.symbols('G w v')
    weights = {2: w, 3: 1 - w - v, 5: v}
    alpha = 1 + sum((weights[m] * s.cancel((s.chebyshevt(m, G) - s.chebyshevt(m, c)) / (G - c)) / s.chebyshevu(m - 1, G) for m in weights))
    beta = sum((weights[m] * s.cancel((s.chebyshevu(m - 1, G) - s.chebyshevu(m - 1, c)) / (G - c)) / s.chebyshevu(m - 1, G) for m in weights))
    der = (s.diff(beta, G) * alpha - beta * s.diff(alpha, G)) / alpha ** 2
    ff = ic.funcs(der, (G, c, w, v))
    stack = [(1, 1.04, -1, 1, 0.36, 0.38, 0, 0.031)]
    accepted = 0
    depth = 0
    while stack:
        box = stack.pop()
        gg, cc, ww, vv = [ic.ball(box[2 * i], box[2 * i + 1]) for i in range(4)]
        bound = 2 * arb((1 - cc * cc).abs_upper()) * (arb(str(box[1])) ** 2 - 1).sqrt() * abs(ff(gg, cc, ww, vv))
        if bound < 2 - cc * cc:
            accepted += 1
            continue
        widths = [box[2 * i + 1] - box[2 * i] for i in range(4)]
        ax = max(range(4), key=lambda i: widths[i])
        mid = (box[2 * ax] + box[2 * ax + 1]) / 2
        if widths[ax] < 1e-05:
            raise ValueError(('monotonicity box', box, str(bound)))
        b1 = list(box)
        b2 = list(box)
        b1[2 * ax + 1] = mid
        b2[2 * ax] = mid
        stack.extend((tuple(b1), tuple(b2)))
    ctx.note('U5 monotonicity certified boxes', accepted)
    ctx.check(True, 'derivation completed', kind='derivation')
