"""Callable exact suite: struct/a8_elim.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp, time
from ..algebra.waves import *

def run(ctx):
    d = ctx.artifacts['square_system']

    def mainfactor(e, deg):
        fs = sp.factor_list(e)[1]
        return [f for f, k in fs if sp.degree(f, W) == deg][0]
    e1 = mainfactor(d['E1'], 2)
    e2 = mainfactor(d['E2'], 4)
    t0 = time.time()
    Res = sp.resultant(e1, e2, W)
    ctx.note('resultant computed', time.time() - t0)
    fl = sp.factor_list(Res)
    ctx.note('factors (degree in X, Y, mult):')
    for f, k in fl[1]:
        ctx.note(sp.degree(f, X), sp.degree(f, Y), k, str(f)[:150])
    ctx.artifacts['two_wave_resultant'] = {'e1': e1, 'e2': e2, 'Res': fl}
    ctx.check(True, 'derivation completed', kind='derivation')
