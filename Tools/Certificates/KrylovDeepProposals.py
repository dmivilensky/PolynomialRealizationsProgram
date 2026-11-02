"""Untrusted exact-integer interval proposals for main_krylov prop:deep.

These numbers become evidence only after the existing Lean integer checker
verifies every operation and its independent actual-source expression.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import json
import argparse
ROWS = [[-1, 6, -5, -7, 2, -2], [0, -2, 8, -7, 2, 6], [-8, -7, -6, 4, 6, -8], [-6, -7, 5, 7, 2, -4], [7, -1, 6, 1, 2, 2], [-8, 2, 2, -4, 6, 2], [-3, 0, -6, 3, -1, -1]]

@dataclass
class Node:
    """One untrusted scaled interval proposal with its actual arithmetic graph location."""
    graph: object
    index: int
    lo: int
    hi: int

    def __add__(self, other):
        """Propose the exact source addition with outward integer rounding."""
        return self.graph.op('add', self, self.graph.coerce(other))

    def __radd__(self, other):
        """Propose source addition with an exact left literal."""
        return self.graph.coerce(other) + self

    def __neg__(self):
        """Propose exact interval negation in the original source graph."""
        return self.graph.op('neg', self)

    def __sub__(self, other):
        """Preserve the original subtraction as addition of a negation."""
        return self + -self.graph.coerce(other)

    def __rsub__(self, other):
        """Propose an exact left-literal subtraction in the original source graph."""
        return self.graph.coerce(other) + -self

    def __mul__(self, other):
        """Propose the original multiplication with exact outward integer rounding."""
        return self.graph.op('mul', self, self.graph.coerce(other))

    def __rmul__(self, other):
        """Propose multiplication by an exact left literal."""
        return self.graph.coerce(other) * self

    def inv(self):
        """Propose the reciprocal on a strictly positive original interval domain."""
        return self.graph.op('inv', self)

    def __truediv__(self, other):
        """Preserve original division as multiplication by the exact reciprocal proposal."""
        return self * self.graph.coerce(other).inv()

    def __rtruediv__(self, other):
        """Propose division of an exact literal by the original interval value."""
        return self.graph.coerce(other) * self.inv()

class Graph:
    """Exact outward-rounded integer proposals for the original rational source arithmetic."""

    def __init__(self, lo, hi, precision=1152, initial=None):
        """Initialize the exact scaled input stack and shared original expression graph."""
        self.unit = 1 << precision
        self.nodes = []
        self.cache = {}
        intervals = initial if initial is not None else [(self.floor(F(lo) * self.unit), self.ceil(F(hi) * self.unit))]
        self.base = len(intervals)
        self.inputs = [Node(self, self.base - 1 - i, a, b) for i, (a, b) in enumerate(intervals)]
        self.input = self.inputs[0]
        self.nonzero = []

    @staticmethod
    def floor(x):
        """Compute the exact integer lower rounding of a rational value."""
        return x.numerator // x.denominator

    @staticmethod
    def ceil(x):
        """Compute the exact integer upper rounding of a rational value."""
        return -(-x.numerator // x.denominator)

    def coerce(self, x):
        """Create or share a canonical exact rational literal proposal."""
        if isinstance(x, Node):
            return x
        q = F(x)
        key = ('literal', q.numerator, q.denominator)
        if key in self.cache:
            return self.cache[key]
        low = self.floor(q * self.unit)
        high = self.ceil(q * self.unit)
        out = Node(self, len(self.nodes) + self.base, low, high)
        self.nodes.append((key, (low, high)))
        self.cache[key] = out
        return out

    def op(self, kind, a, b=None):
        """Propose an original field operation using only exact integer interval arithmetic."""
        key = (kind, a.index) if b is None else (kind, a.index, b.index)
        if key in self.cache:
            return self.cache[key]
        if kind == 'add':
            low, high = (a.lo + b.lo, a.hi + b.hi)
        elif kind == 'neg':
            low, high = (-a.hi, -a.lo)
        elif kind == 'mul':
            xs = [x * y for x in (a.lo, a.hi) for y in (b.lo, b.hi)]
            low = min(xs) // self.unit
            high = -(-max(xs) // self.unit)
        elif kind == 'inv':
            if a.lo <= 0:
                raise ArithmeticError(f'nonpositive inverse node {a.index}: [{float(F(a.lo, self.unit))},{float(F(a.hi, self.unit))}]')
            low = self.unit * self.unit // a.hi
            high = -(-self.unit * self.unit // a.lo)
            self.nonzero.append(a.index)
        else:
            raise ValueError(kind)
        out = Node(self, len(self.nodes) + self.base, low, high)
        self.nodes.append((key, (low, high)))
        self.cache[key] = out
        return out

    def code(self):
        """Translate original absolute graph locations to the existing checker reverse-stack offsets."""
        out = []
        for j, (op, bounds) in enumerate(self.nodes):
            if op[0] == 'literal':
                out.append((op, bounds))
            else:
                out.append(((op[0], *(self.base + j - 1 - i for i in op[1:])), bounds))
        return out

def sumv(xs, G):
    """Preserve the independently specified right-associated finite sum and its exact zero tail."""
    if not xs:
        return G.coerce(0)
    return xs[0] + sumv(xs[1:], G)

def dot(a, b, G):
    """Preserve the original finite Euclidean pairing expression."""
    return sumv([x * y for x, y in zip(a, b)], G)

def va(a, b):
    """Preserve the original coordinatewise vector addition."""
    return [x + y for x, y in zip(a, b)]

def vn(a):
    """Preserve the original coordinatewise vector negation."""
    return [-x for x in a]

def vs(a, b):
    """Preserve vector subtraction as its original addition and negation expression."""
    return va(a, vn(b))

def vm(t, a):
    """Preserve the original scalar-vector expression."""
    return [t * x for x in a]

def ma(a, b):
    """Preserve original pointwise physical matrix addition."""
    return [va(x, y) for x, y in zip(a, b)]

def mm(t, a):
    """Preserve original scalar multiplication of a physical matrix."""
    return [vm(t, row) for row in a]

def mv(a, x, G):
    """Preserve the original finite matrix-vector multiplication expression."""
    return [dot(row, x, G) for row in a]

def tr(a):
    """Arrange the original augmented source vectors as actual matrix columns."""
    return list(map(list, zip(*a)))

def det(a, G):
    """Preserve the independently specified finite Laplace determinant expression."""
    if not a:
        return G.coerce(1)
    return sumv([G.coerce((-1) ** j) * a[0][j] * det([row[:j] + row[j + 1:] for row in a[1:]], G) for j in range(len(a))], G)

def adj(a, G):
    """Preserve the original signed-minor adjugate expression and its index convention."""
    n = len(a)
    return [[G.coerce((-1) ** (j + i)) * det([row[:i] + row[i + 1:] for r, row in enumerate(a) if r != j], G) for j in range(n)] for i in range(n)]

def inv(a, G):
    """Propose the reciprocal on a strictly positive original interval domain."""
    return mm(det(a, G).inv(), adj(a, G))

def block(row):
    """Evaluate the original physical positive-root transport of one exact rational source row."""
    a, b, c, d, e, f = row
    out = [[a, b, 0, 0], [b, c, 0, 0], [0, 0, d, e], [0, 0, e, f]]
    return [[F(out[i][j] * (i + 1) * (j + 1), 32000) for j in range(4)] for i in range(4)]

def execute_stage(k, initial):
    """Propose one genuine original RFC phase from its actual input coordinate layout.

The original direction, negative correction solve, measured total-step and
secant updates retain exactly the independently defined Lean expression tree.
The returned intervals are proposals; only Lean kernel acceptance proves bounds."""
    G = Graph(0, 0, initial=initial)
    s = G.input
    blocks = [[[G.coerce(x) for x in row] for row in block(r)] for r in ROWS]
    inc = [ma(mm(G.coerce(1) - s, blocks[0]), mm(s, blocks[1])), blocks[2], blocks[3]]
    A = [[G.coerce((i + 1) ** 2 if i == j else 0) for j in range(4)] for i in range(4)]
    for j in range(k):
        A = ma(A, inc[j])
    if k == 0:
        g = list(map(G.coerce, [1, 2, F(3, 10 ** 12), F(4, 10 ** 12)]))
        S = []
        Y = []
    else:
        g = G.inputs[1:5]
        S = [G.inputs[5 + 4 * i:9 + 4 * i] for i in range(k)]
        Y = [G.inputs[5 + 4 * k + 4 * i:9 + 4 * k + 4 * i] for i in range(k)]
    checks = {}
    co = []
    if k:
        cross = [[dot(y, u, G) for u in S] for y in Y]
        co = mv(inv(cross, G), [dot(y, g, G) for y in Y], G)
    synthesis = [sumv([co[j] * S[j][i] for j in range(k)], G) for i in range(4)]
    d = va(vn(g), synthesis)
    z = mv(A, d, G)
    curv = dot(d, z, G)
    alpha = -dot(g, d, G) / curv
    line = vm(alpha, d)
    gp = va(g, vm(alpha, z))
    U = [d] + S
    Z = [z] + Y
    H = [[dot(U[max(i, j)], Z[min(i, j)], G) for j in range(k + 1)] for i in range(k + 1)]

    def defect(us, ys):
        """Preserve the original nested row/column squared-defect sums and positive energy denominators."""
        energies = [dot(u, y, G) for u, y in zip(us, ys)]
        return sumv([sumv([(dot(us[i], ys[j], G) - dot(us[j], ys[i], G)) * (dot(us[i], ys[j], G) - dot(us[j], ys[i], G)) / (energies[i] * energies[j]) for j in range(len(us))], G) for i in range(len(us))], G)
    checks['alpha'] = alpha
    checks['curvature'] = curv
    checks['augDefect'] = defect(U, Z)
    checks['oldDefect'] = defect(S, Y)
    checks['modelDet'] = det(H, G)
    for i in range(k + 1):
        checks['energy' + str(i)] = dot(U[i], Z[i], G)
    for i in range(4):
        checks['direction' + str(i)] = d[i]
        checks['probe' + str(i)] = z[i]
        checks['post' + str(i)] = gp[i]
    if k == 3:
        hc = [dot(u, gp, G) for u in U]
        adjhc = mv(adj(H, G), hc, G)
        uadj = [sumv([adjhc[j] * U[j][i] for j in range(4)], G) for i in range(4)]
        B = ma(A, blocks[6])
        v = mv(B, uadj, G)
        checks['vSquare'] = dot(v, v, G)
        checks['gPrimeSquare'] = dot(gp, gp, G)
        checks['basisDet'] = det(tr(U), G)
        for i in range(4):
            checks['numerator' + str(i)] = v[i]
        for j in (1, 2, 3):
            checks['leading' + str(j)] = det([row[:j] for row in H[:j]], G)
        return (G, checks, None)
    u = [G.coerce(0)] * 4
    if k:
        co = vn(mv(inv(H, G), [dot(u, gp, G) for u in U], G))
        u = [sumv([co[j] * U[j][i] for j in range(k + 1)], G) for i in range(4)]
    B = ma(A, blocks[4] if k == 1 else blocks[5] if k == 2 else [[G.coerce(0)] * 4 for _ in range(4)])
    gn = va(gp, mv(B, u, G))
    Sn = [va(line, u)] + S
    Yn = [vs(gn, g)] + Y
    fields = [G.input] + gn + [x for row in Sn for x in row] + [x for row in Yn for x in row]
    for i, v in enumerate(fields):
        checks['nextInput' + str(i)] = v
    return (G, checks, fields)

def main():
    """Regenerate the twelve exact interval proposals for the fixed original dyadic source family."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='Directory for untrusted exact JSON enclosure proposals')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    lo = F(2646454928180481456171251146847918056121676983675537773643408674368639160074972432041573143760250154588367653162907394362391485, 2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576)
    hi = F(1323227464090240728085625573423959028060838491837768886821704337184319580037486216020786571880125077294183826581453697181195743, 1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288)
    for name, a, b in [('interval', lo, hi), ('left', lo, lo), ('right', hi, hi)]:
        initial = [(Graph.floor(a * (1 << 1152)), Graph.ceil(b * (1 << 1152)))]
        for k in range(4):
            graph, checks, fields = execute_stage(k, initial)
            proposal = {'scale': graph.unit, 'initial': initial, 'nodes': graph.code(), 'checks': {key: graph.base + len(graph.nodes) - 1 - value.index for key, value in checks.items()}, 'operations': len(graph.nodes)}
            (args.output / f'krylov_deep_{name}_stage{k}.json').write_text(json.dumps(proposal))
            if k < 3:
                initial = [(value.lo, value.hi) for value in fields]
            print(f'{name} phase {k}: {len(graph.nodes)} exact proposed operations')
if __name__ == '__main__':
    main()
