"""Propose compact rational enclosures for the finite rational-angle constants."""
from fractions import Fraction
import mpmath as mp

POINTS = tuple(sorted({(j, 13) for j in range(13)} |
                      {(1, 3), (1, 4), (1, 5), (2, 5),
                       (3, 18), (4, 18), (3, 21), (4, 21), (5, 21)}))


def q(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def build_payload():
    mp.mp.dps = 80
    denominator = 10**14
    points = []
    for j, k in POINTS:
        entry = {"j": j, "k": k, "taylor_terms": 32}
        for name, function in (("sin", mp.sin), ("cos", mp.cos)):
            integer = int(mp.floor(function(2*mp.pi*j/k)*denominator))
            entry[name] = [q(Fraction(integer-1, denominator)),
                           q(Fraction(integer+2, denominator))]
        points.append(entry)
    return {"schema": "heavy-ball-rational-trigonometry-v1", "points": points}
