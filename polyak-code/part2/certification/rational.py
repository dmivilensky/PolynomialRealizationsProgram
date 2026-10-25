"""Compact exact rational proposals for the two rational examples.

No prover code is exported: coefficients, partition and subdivision depths are
mathematical data, independently checked by each downstream verifier.
"""
from fractions import Fraction as F
from math import comb


def _q(x):
    x = F(x)
    return [x.numerator, x.denominator]


def _bernstein(p, a, b):
    n = len(p) - 1
    power = [sum(p[k]*comb(k,j)*a**(k-j)*(b-a)**j for k in range(j,n+1))
             for j in range(n+1)]
    return [sum(power[j]*F(comb(i,j),comb(n,j)) for j in range(i+1))
            for i in range(n+1)]


def _mul(a,b):
    p=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): p[i+j] += x*y
    return p


def build_payload():
    xi = [F(88897198775653,91052250190902),F(242832333719,122711927481),
          -F(26156560000,8676600933)]
    neg = [-x for x in xi]
    sq = [-x for x in _mul(xi,xi)]
    sq[0]+=3; sq[2]-=3
    cells=[]
    # A deterministic exact partition. There are no floating-point sign tests.
    def cover(a,b):
        for name,p in [('negativeXi',neg),('squaredGap',sq)]:
            if min(_bernstein(p,a,b)) > 0:
                cells.append({'lo':_q(a),'hi':_q(b),'test':name,'depth':0})
                return
        m=(a+b)/2
        if b-a < F(1,2**20): raise ValueError('floor partition did not certify')
        cover(a,m);cover(m,b)
    cover(F(-1),F(1))
    sextic=[F(45613,1898100),-F(92371789,208791000),F(1007042,347985),
            -F(34149683,5219775),F(389324,94905),F(23608,7733),-F(644800,208791)]
    def accepts(p,a,b,d):
        return min(_bernstein(p,a,b)) > 0 or (d>0 and
            accepts(p,a,(a+b)/2,d-1) and accepts(p,(a+b)/2,b,d-1))
    depth=0
    while not accepts(sextic,F(-1),F(1),depth):
        depth+=1
        if depth>12: raise ValueError('convergence sextic failed')
    return {'schema':'heavy-ball-rational-examples-v1',
            'thirteen':{'tuning':[_q(100),_q(F(70471,31800)),_q(F(6169,9900))],
                        'nu_weights':[_q(F(149,797)),_q(F(648,797))],
                        'frequency_numerators':[2,3],'frequency_denominator':13,
                        'xi_coefficients':list(map(_q,xi)),'floor_cells':cells},
            'convergence':{'tuning':[_q(100),_q(F(111,50)),_q(F(31,50))],
                           'lag':4,'ratio':_q(F(13,100)),'margin':_q(F(1,1000)),
                           'sextic_coefficients':list(map(_q,sextic)),
                           'bernstein_depth':depth}}
