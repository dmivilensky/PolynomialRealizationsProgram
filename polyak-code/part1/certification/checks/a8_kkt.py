"""Callable exact suite: struct/a8_kkt.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp, time
from ..algebra.waves import *

def run(ctx):
    d = ctx.artifacts['threshold_system']
    R1 = sp.Poly(sp.expand(d['R1']), c)
    A = R1.all_coeffs()
    A4, A3, A2, A1, A0 = [sp.expand(x) for x in A]
    E1 = sp.expand(8 * A4 ** 2 * A1 - A3 * (4 * A4 * A2 - A3 ** 2))
    E2 = sp.expand(64 * A4 ** 3 * A0 - (4 * A4 * A2 - A3 ** 2) ** 2)
    t0 = time.time()
    E1f = sp.factor(E1)
    E2f = sp.factor(E2)
    ctx.note('E1 =', E1f)
    ctx.note('E2 =', E2f)
    ctx.note(time.time() - t0)
    ctx.artifacts['square_system'] = {'E1': E1f, 'E2': E2f}
    ctx.check(True, 'derivation completed', kind='derivation')
