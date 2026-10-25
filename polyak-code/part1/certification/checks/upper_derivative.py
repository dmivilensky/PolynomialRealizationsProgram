"""Callable exact suite: upper/star_ineq.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp, time
from ..algebra.bernstein import certify_positive

def run(ctx):
    G, c, W = sp.symbols('G c W')
    N = W * (4 * G ** 2 - 1) + 4 * (1 - W) * G * (G + c)
    M = 8 * G ** 3 + 4 * G ** 2 * c - G + (1 - W) * (4 * G * c ** 2 - 3 * G) - W * (G + c)
    ctx.check(sp.expand(M.subs(W, 0) - 4 * G * (2 * G ** 2 + G * c + c ** 2 - 1)) == 0, 'upper/star_ineq.py:14: sp.expand(M.subs(W, 0) - 4 * G * (2 * G ** 2 + G * c + c ** 2 - 1)) == 0')
    ctx.check(sp.expand(M.subs(W, 1) - (4 * G ** 2 - 1) * (2 * G + c)) == 0, 'upper/star_ineq.py:15: sp.expand(M.subs(W, 1) - (4 * G ** 2 - 1) * (2 * G + c)) == 0')
    num = sp.expand(sp.diff(N, G) * M - N * sp.diff(M, G))
    ctx.check(sp.expand(num - (2 * W ** 2 + 4 * W * (16 * G ** 3 * c + 8 * G ** 2 - 1) - 16 * G ** 2 * (2 * G ** 2 + 4 * G * c + 1))) == 0, 'upper/star_ineq.py:17: sp.expand(num - (2 * W ** 2 + 4 * W * (16 * G ** 3 * c + 8 * G ** 2 - 1) - 16 * G ** 2 * (2 * G ** 2 + 4 * G * c + 1))) == 0')
    box = [(1, sp.Rational(3, 2)), (-1, 1), (0, 1)]
    T0 = time.time()
    for Mi in (M.subs(W, 0), M.subs(W, 1)):
        ok, info = certify_positive(Mi, (G, c), box[:2])
        ctx.note('M>0 at W endpoint:', ctx.check(ok, 'upper/star_ineq.py:22: ok'), info)
        ctx.check(ok, 'upper/star_ineq.py:22: ok')
    Pi = sp.expand((2 - c ** 2) ** 2 * M ** 4 - 4 * (1 - c ** 2) ** 2 * (G ** 2 - 1) * num ** 2)
    ok, info = certify_positive(Pi, (G, c, W), box)
    ctx.note('(*) Pi > 0 on [1,3/2]x[-1,1]x[0,1]:', ctx.check(ok, 'upper/star_ineq.py:25: ok'), info, '%.1fs' % (time.time() - T0))
    ctx.check(ok, 'upper/star_ineq.py:26: ok')
    ctx.check(True, 'derivation completed', kind='derivation')
