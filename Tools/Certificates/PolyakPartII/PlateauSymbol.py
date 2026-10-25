"""Exact aligned polynomial proposals for the selected global dual symbols.

The rational source arrays are regenerated locally and independently checked
against maintained Chebyshev/quotient recurrences. No exporter code is executed.
"""
from fractions import Fraction as F
from pathlib import Path
from .Payload import rational

OUTPUTS=frozenset({'polyak/Certificates/PartII/Plateaus/SymbolData.lean',
                   'polyak/Certificates/PartII/Plateaus/SymbolChecks.lean'})


def _q(q):
    q=F(q)
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'


def _trim(p):
    while len(p)>1 and p[-1]==0:p.pop()
    return p


def _add(a,b):
    return _trim([(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0))
                  for i in range(max(len(a),len(b)))])


def _scale(p,a):return [a*x for x in p]


def _mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return _trim(out)


def _cheb(n,kind):
    a,b=[F(1)],[F(0),F(1 if kind=='T' else 2)]
    for _ in range(n):a,b=b,_add([F(0)]+_scale(b,2),_scale(a,-1))
    return a


def _quotient(n):
    if n==0:return [F(0)]
    p=_scale(_cheb(n,'T'),-1);p[0]+=1
    out=[F(0)]*n
    for i in range(n-1,-1,-1):out[i]=-p[i+1]+(out[i+1] if i+1<n else 0)
    if out[0]!=p[0]:raise ValueError('quotient identity failed')
    return out


def _components(n):
    W=_quotient(abs(n))
    return [W,[F(0)]+W,[F(0),F(0)]+W,
            _scale(_mul([F(1),F(1)],_cheb(abs(n)-1,'U')),-1 if n>0 else 1)]


def _derivative(p,order):
    for _ in range(order):p=[i*p[i] for i in range(1,len(p))] or [F(0)]
    return p


def generate(payload,stagingRoot):
    if not isinstance(payload,dict) or payload.get('schema')!='heavy-ball-selected-plateaus-v1':
        raise ValueError('invalid plateau symbol schema')
    cases={row['name']:row for row in payload['rows']}
    expected={'2/9':(18,[1,19,-4,14],2),'5/21':(21,[1,-20,-12,9,-4,-25],3)}
    if set(cases)!=set(expected):raise ValueError('missing plateau symbol rows')
    data=['import polyak.CertifiedExamples.Plateaus.SymbolCover',
          'import polyak.Certificates.PartII.Plateaus.Data','',
          '/-! Independent rational component tables and a finite contact cover. -/',
          'namespace polyak.Certificates.PartII.Plateaus',
          'open LeanCert.Engine LeanCert.Core polyak.CertifiedExamples.Plateaus','']
    checks=['import polyak.Certificates.PartII.Plateaus.SymbolData','',
            '/-! Every source identity and every global Bernstein bound is checked by the ordinary kernel. -/',
            'namespace polyak.Certificates.PartII.Plateaus',
            'open polyak.CertifiedExamples.Plateaus','']
    for name,(L,lags,d) in expected.items():
        row=cases[name];tag=f'row{L}';degree=max(map(abs,lags))+1
        if [n for pair in row['pairs'] for n in pair]!=lags:raise ValueError('dual source lags changed')
        for order in (0,2):
            polys=[_derivative(p,order) for n in lags for p in _components(n)]
            arrays=[]
            for p in polys:
                if len(p)>degree+1:raise ValueError('component degree overflow')
                p=p+[F(0)]*(degree+1-len(p))
                arrays.append('⟨#['+','.join(_q(q) for q in p)+']⟩')
            data += [f'def {tag}Family{order} : Fin {len(polys)} → QPoly :=',
                     '  !['+',\n    '.join(arrays)+']','']
            checks += [f'theorem {tag}Family{order}_identity :',
                       f'    familyIdentityCheck {tag}Lags {order} {tag}Family{order}=true := by kernel_decide','']
        cells=[]
        for cell in row['symbol_cells']:
            lo,hi=rational(cell['lo']),rational(cell['hi'])
            if lo>hi:raise ValueError('reversed symbol cover cell')
            if cell['kind']=='value':marker='none'
            elif cell['kind']=='curvature':
                choices=[i for i,C in enumerate(row['cosine_boxes'])
                         if lo<=rational(C[0]) and rational(C[1])<=hi]
                if len(choices)!=1:raise ValueError('curvature cell must enclose one actual support box')
                marker=f'(some ⟨{choices[0]},by decide⟩)'
            else:raise ValueError('invalid symbol cover cell kind')
            cells.append(f'(⟨{_q(lo)},{_q(hi)},by norm_num⟩,{marker})')
        data += [f'def {tag}Cover : List (CoverCell {d}) :=',
                 '  ['+',\n   '.join(cells)+']','']
        checks += [f'theorem {tag}Cover_checked :',
                   f'    coverCheck {tag}Xi {tag}DualBoxes {tag}Cosines {tag}Family0 {tag}Family2',
                   f'      {degree+1} {tag}Cover=true := by kernel_decide','']
    data+=['end polyak.Certificates.PartII.Plateaus','']
    checks+=['end polyak.Certificates.PartII.Plateaus','']
    for relative,lines in [('polyak/Certificates/PartII/Plateaus/SymbolData.lean',data),
                           ('polyak/Certificates/PartII/Plateaus/SymbolChecks.lean',checks)]:
        path=Path(stagingRoot)/relative;path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text('\n'.join(lines),encoding='utf-8')
    return sorted(OUTPUTS)
