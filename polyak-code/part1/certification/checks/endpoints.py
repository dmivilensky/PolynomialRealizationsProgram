"""Callable exact suite: regimes/endpoints.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as s, mpmath as mp, json
from pathlib import Path
from flint import arb, ctx as arb_context
from ..interval import funcs, inside
from ..algebra.systems import p1, p2, central, G, u, c, z

from ..precision import local_precision

@local_precision(bits=256,digits=90)
def run(ctx):
    dat = ctx.artifacts['p2_field']
    Ha = 162529280000 * G ** 12 - 238685519872 * G ** 10 + 77668708352 * G ** 8 - 6246545408 * G ** 6 - 58821872 * G ** 4 + 12933112 * G ** 2 + 229441
    H1 = 32 * G ** 3 - 36 * G ** 2 + 4 * G - 1

    def rational(q):
        return arb(int(s.numer(q))) / int(s.denom(q))

    def isolate(poly, lo, hi):
        roots = s.Poly(poly, G).intervals(eps=s.Rational(1, 10 ** 65), inf=lo, sup=hi)
        ctx.check(len(roots) == 1 and roots[0][1] == 1, 'regimes/endpoints.py:14: len(roots) == 1 and roots[0][1] == 1')
        a, b = map(rational, roots[0][0])
        return arb((a + b) / 2, (b - a) / 2)
    ga = isolate(Ha, s.Rational(102358, 100000), s.Rational(102359, 100000))
    g1 = isolate(H1, s.Rational(103329, 100000), s.Rational(103330, 100000))
    fp = funcs(dat['P'], (G, u))
    fpu = funcs(s.diff(dat['P'], u), (G, u))
    fpm = s.lambdify((G, u), dat['P'], 'mpmath')

    def physical(g):
        gm = mp.mpf(g.mid().str(90, radius=False))
        um = mp.findroot(lambda vv: fpm(gm, vv), mp.mpf('.512'))
        uc = arb(str(um))
        uu = arb(uc, arb('1e-55'))
        inv = 1 / fpu(arb(g.mid()), uc)
        kk = uc - inv * fp(g, uc) + (1 - inv * fpu(g, uu)) * (uu - uc)
        ctx.check(inside(kk, uu), 'regimes/endpoints.py:24: inside(kk, uu)')
        vals = {k: funcs(v, (G, u))(g, uu) for k, v in dat.items() if k != 'P'}
        disc = vals['a'] ** 2 - 4 * vals['b']
        ctx.check(disc > 0, 'regimes/endpoints.py:26: disc > 0')
        x = (-vals['a'] - disc.sqrt()) / 2
        y = (-vals['a'] + disc.sqrt()) / 2
        p = (vals['mc'] - x) / (y - x)
        return ([uu, x, y, p, vals['d'], vals['W']], vals['s5'])

    def identify(name, par, point):
        boxes = ctx.artifacts[name + '_boxes.json']
        for b in boxes:
            if par.lower() >= arb(str(b['a'])) and par.upper() <= arb(str(b['b'])):
                X = [arb(arb(str(x)), arb(str(r))) for x, r in zip(b['center'], b['radii'])]
                ctx.check(all((inside(x, xx) for x, xx in zip(point, X))), 'regimes/endpoints.py:35: all((inside(x, xx) for x, xx in zip(point, X)))')
                ctx.note('identified', name, str(par), flush=True)
                return
        raise AssertionError(('no box', name, str(par)))
    par, vs, F, Q, su = p1()
    zw = s.sqrt(3) - 1
    ctx.check(all((s.simplify(f.subs({z: zw, vs[0]: 0, vs[1]: -1 / (2 * zw)})) == 0 for f in F)), 'regimes/endpoints.py:40: all((s.simplify(f.subs({z: zw, vs[0]: 0, vs[1]: -1 / (2 * zw)})) == 0 for f in F))')
    zwi = arb(3).sqrt() - 1
    identify('p1', zwi, [arb(0), -1 / (2 * zwi)])
    par, vs, F, Q, su = p2()
    us = 1 - 1 / (2 * G)
    xs = -1 / (2 * G)
    ys = (2 * G - 1) / (4 * G)
    gs = (2 * G - 1) / (2 * G * G)
    ds = gs * (G * G - 1) / G
    ws = 2 * (1 + 2 * G - 2 * G * G) / (4 * G + 1)
    exact = [us, xs, ys, 0, ds, ws]
    for f in F:
        num = s.cancel(f.subs(dict(zip(vs, exact)))).as_numer_denom()[0]
        ctx.check(s.rem(s.Poly(num, G), s.Poly(H1, G)).is_zero, 'regimes/endpoints.py:49: s.rem(s.Poly(num, G), s.Poly(H1, G)).is_zero')
    point = [funcs(e, (G,))(g1) if not isinstance(e, int) else arb(e) for e in exact]
    identify('p2', g1, point)
    lo = arb(1023581427007) / 10 ** 12
    hi = arb(1023581427009) / 10 ** 12
    ctx.check(physical(lo)[1] < 0 and physical(hi)[1] > 0, 'regimes/endpoints.py:55: physical(lo)[1] < 0 and physical(hi)[1] > 0')
    aa, sl5 = physical(ga)
    identify('p2', ga, aa)
    uv, xv, yv, pv, dv, W = aa
    hh = ga - 1
    point5 = [(uv - arb('.5')) / hh, (xv + arb('.5')) / hh, yv, pv / hh, dv / hh, W, 1 - W]
    identify('central', hh, point5)
    ctx.check(aa[3] > 0 and aa[3] < 1 and (aa[5] > 0) and (aa[5] < 1), 'regimes/endpoints.py:60: aa[3] > 0 and aa[3] < 1 and (aa[5] > 0) and (aa[5] < 1)')
    ctx.note('ALL ENDPOINT IDENTITIES AND BRANCH IDENTIFICATIONS PASSED')
    ctx.check(True, 'derivation completed', kind='derivation')
