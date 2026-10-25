"""Theorem 8.6 (convexity): exact symbolic verification of the formulas of its proof.

With Xi(c) = X0 + X1 c + X2 c^2, c = cos w and h = Xi(cos w)/sin w:
  (1) h' = -((X1 + 2 X2 c)(1 - c^2) + Xi(c) c)/sin^2 w;
  (2) h'' sin^3 w = X0 (1 + c^2) + 2 X1 c + X2 (c^4 - c^2 + 2);
  (3) X0 (1 + c^2) + 2 X1 c + X2 (c^4 - c^2 + 2)
        = (1 + c)^2 Xi(1)/2 + (1 - c)^2 Xi(-1)/2 + X2 (1 - c^2)^2   (polynomial identity);
  (4) the leading coefficient of the quadratic Xi of (6.4) is -2 beta/(B (1 - beta));
  (5) for u = h + s and Theta = arccot u: Theta' = -u'/(1 + u^2), Theta'' = -u''/(1 + u^2) + 2 u u'^2/(1 + u^2)^2.

Usage: python3 convexity.py
"""
import sys
import sympy as sp

w = sp.symbols('omega', real=True)
X0, X1, X2, c, s, b, B, A = sp.symbols('X0 X1 X2 c s beta B A', real=True)
Xi = lambda cc: X0 + X1 * cc + X2 * cc ** 2
FAILED = []


def report(name, ok):
    print(('OK    ' if ok else 'FAIL  ') + name)
    if not ok:
        FAILED.append(name)


def main():
    h = Xi(sp.cos(w)) / sp.sin(w)
    cw = sp.cos(w)
    hp = -((X1 + 2 * X2 * cw) * (1 - cw ** 2) + Xi(cw) * cw) / sp.sin(w) ** 2
    report("(1) h' = -((X1 + 2 X2 c)(1 - c^2) + Xi(c) c)/sin^2 w", sp.simplify(sp.diff(h, w) - hp) == 0)
    hpp = (X0 * (1 + cw ** 2) + 2 * X1 * cw + X2 * (cw ** 4 - cw ** 2 + 2)) / sp.sin(w) ** 3
    report("(2) h'' sin^3 w = X0 (1 + c^2) + 2 X1 c + X2 (c^4 - c^2 + 2)", sp.simplify(sp.diff(h, w, 2) - hpp) == 0)
    lhs = X0 * (1 + c ** 2) + 2 * X1 * c + X2 * (c ** 4 - c ** 2 + 2)
    rhs = (1 + c) ** 2 * Xi(1) / 2 + (1 - c) ** 2 * Xi(-1) / 2 + X2 * (1 - c ** 2) ** 2
    report('(3) the expression in Xi(1), Xi(-1) and X2 (polynomial identity)', sp.expand(lhs - rhs) == 0)
    XiA = (B ** 2 - (1 - b) ** 2 - A ** 2 + 2 * A * (1 + b) * c - 4 * b * c ** 2) / (2 * B * (1 - b))
    report('(4) X2 = -2 beta/(B (1 - beta))', sp.simplify(sp.Poly(sp.together(XiA) * 2 * B * (1 - b), c).coeff_monomial(c ** 2)
                                                        / (2 * B * (1 - b)) + 2 * b / (B * (1 - b))) == 0)
    u = sp.Function('u')(w)
    Th = sp.acot(u)
    up, upp = sp.diff(u, w), sp.diff(u, w, 2)
    ok5 = (sp.simplify(sp.diff(Th, w) + up / (1 + u ** 2)) == 0 and
           sp.simplify(sp.diff(Th, w, 2) - (-upp / (1 + u ** 2) + 2 * u * up ** 2 / (1 + u ** 2) ** 2)) == 0)
    report("(5) Theta' and Theta'' for Theta = arccot u", ok5)
    if FAILED:
        print('CHECK FAILED', ', '.join(FAILED))
        sys.exit(1)
    print('ALL OK')


if __name__ == '__main__':
    main()
