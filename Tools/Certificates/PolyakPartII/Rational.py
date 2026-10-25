"""Translate exact JSON rational proposals into kernel-checked Lean data."""
from fractions import Fraction as F
from pathlib import Path

OUTPUTS = frozenset({'polyak/Certificates/PartII/Rational/Polynomials.lean',
                     'polyak/Certificates/PartII/Rational/Slacks.lean'})


def _q(v):
    if not isinstance(v,list) or len(v)!=2 or type(v[0]) is not int or type(v[1]) is not int or v[1]<=0:
        raise ValueError('invalid rational pair')
    q=F(*v)
    if [q.numerator,q.denominator]!=v: raise ValueError('noncanonical rational')
    return q


def _lean(q):
    q=F(q)
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'


def _horner(p):
    text='0'
    for q in reversed(p): text=f'C ({_lean(q)})+X*({text})'
    return text


def generate(payload,stagingRoot):
    if (not isinstance(payload,dict) or set(payload)!={'schema','thirteen','convergence'}
            or payload['schema']!='heavy-ball-rational-examples-v1'):
        raise ValueError('rational schema')
    thirteen,convergence=payload['thirteen'],payload['convergence']
    if (not isinstance(thirteen,dict) or set(thirteen)!={'tuning','nu_weights',
            'frequency_numerators','frequency_denominator','xi_coefficients','floor_cells'}
            or not isinstance(convergence,dict) or set(convergence)!={'tuning','lag','ratio',
            'margin','sextic_coefficients','bernstein_depth'}):
        raise ValueError('rational example fields changed')
    if (list(map(_q,thirteen['tuning'])) != [F(100),F(70471,31800),F(6169,9900)]
            or list(map(_q,thirteen['nu_weights'])) != [F(149,797),F(648,797)]
            or thirteen['frequency_numerators'] != [2,3] or thirteen['frequency_denominator'] != 13
            or list(map(_q,convergence['tuning'])) != [F(100),F(111,50),F(31,50)]
            or convergence['lag'] != 4 or _q(convergence['ratio']) != F(13,100)
            or _q(convergence['margin']) != F(1,1000)):
        raise ValueError('rational example source parameters changed')
    p=list(map(_q,payload['thirteen']['xi_coefficients']))
    sext=list(map(_q,payload['convergence']['sextic_coefficients']))
    if len(p)!=3 or len(sext)!=7:raise ValueError('source polynomial degree changed')
    floor_cells=thirteen['floor_cells']
    if not isinstance(floor_cells,list) or not 1<=len(floor_cells)<=256:
        raise ValueError('invalid floor partition')
    def code(name,coeff,source):
        return f'''def {name} : Numerics.PolynomialCode ({source}) where
  code := ⟨#[{','.join(_lean(q) for q in coeff)}]⟩
  exact := by
    change {_horner(coeff)} = _
    norm_num [floorPolynomial, thirteenXiSource, convergenceSexticSource]
    ring

'''
    text='''import polyak.Farey.Examples.FloorCertificate
import polyak.Numerics.KernelDecide

/-! Exact rational data from the external Heavy-Ball archive. Each coefficient
identity, Bernstein sign and covering predicate is checked by Lean's kernel. -/
namespace polyak.Certificates.PartII.Rational
open polyak polyak.Farey.Examples LeanCert.Core LeanCert.Engine Polynomial
open scoped Polynomial

'''
    text+=code('xiCode',p,'thirteenXiSource')
    text+='''def negativeXiCode : Numerics.PolynomialCode (floorPolynomial thirteenXiSource .negativeXi) where
  code := QPoly.mul (QPoly.constant (-1)) xiCode.code
  exact := by
    rw [QPoly.toPoly_mul,QPoly.toPoly_constant,xiCode.exact]
    simp [floorPolynomial]

def squaredGapCode : Numerics.PolynomialCode (floorPolynomial thirteenXiSource .squaredGap) where
  code := QPoly.add
    (QPoly.mul (QPoly.constant 3)
      (QPoly.add (QPoly.constant 1) (QPoly.mul (QPoly.constant (-1)) (QPoly.mul QPoly.X QPoly.X))))
    (QPoly.mul (QPoly.constant (-1)) (QPoly.mul xiCode.code xiCode.code))
  exact := by
    simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,xiCode.exact]
    norm_num [floorPolynomial]
    ring

'''
    cells=[]
    for i,C in enumerate(floor_cells):
        if not isinstance(C,dict) or set(C)!={'lo','hi','test','depth'}:
            raise ValueError('invalid floor cell fields')
        lo,hi=_q(C['lo']),_q(C['hi']); test=C['test'];depth=C['depth']
        if test not in ('negativeXi','squaredGap') or type(depth)is not int or not 0<=depth<=12 or lo>hi:
            raise ValueError('invalid floor cell')
        name=f'floorCell{i:02d}';cells.append(name)
        text+=f'''def {name} : FloorCell thirteenXiSource where
  interval := ⟨{_lean(lo)},{_lean(hi)},by norm_num⟩
  test := .{test}
  code := {test}Code
  depth := {depth}
  checked := by kernel_decide

'''
    text+='''def thirteenFloor : FloorCertificate thirteenXiSource where
  cells := ['''+','.join(cells)+''']
  covered := by kernel_decide

theorem thirteen_phase_floor :
    ∀ ω ∈ Set.Icc (0:ℝ) Real.pi, Real.pi/6 < thirteenTuning.angle ω :=
  thirteen_floor_of_certificate thirteenFloor

'''
    text+=code('convergenceCode',sext,'convergenceSexticSource')
    depth=payload['convergence']['bernstein_depth']
    if type(depth)is not int or not 0<=depth<=12:raise ValueError('invalid sextic depth')
    text+=f'''theorem convergence_checked :
    QPoly.bernsteinCheck .strictLower convergenceCode.code 0 ⟨-1,1,by norm_num⟩ {depth}=true := by
  kernel_decide

theorem convergence_positive (c:ℝ) (hc:c∈Set.Icc (-1:ℝ) 1) :
    0<convergenceSextic c := by
  rw [←convergence_sextic_source_exact]
  exact convergenceCode.positive ⟨-1,1,by norm_num⟩ {depth} convergence_checked c (by
    simpa only [IntervalRat.mem_def,Rat.cast_neg,Rat.cast_one] using And.intro hc.1 hc.2)

theorem convergence_rate_lt_one : convergenceTuning.rate<1 :=
  convergence_from_sextic_positive convergence_positive

end polyak.Certificates.PartII.Rational
'''
    relative='polyak/Certificates/PartII/Rational/Polynomials.lean';path=Path(stagingRoot)/relative
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text,encoding='utf-8')
    slacks='''import polyak.CertifiedExamples.Rational.ThirteenBounds
import polyak.Numerics.KernelDecide

/-! Exact arithmetic acceptance of the archived root-of-unity coordinate boxes.
The source formula and all integer-lag reduction are independent maintained proofs. -/
namespace polyak.Certificates.PartII.Rational
open CertifiedExamples.Rational Farey.Examples chebyshev2.Numerics

theorem thirteen_min_checked :
    (IntervalExpr.neg normalizedMinExpression).strictNegative thirteenBox=true := by kernel_decide

'''
    for n in range(1,13):
        slacks+=f'''theorem thirteen_lag{n:02d}_checked :
    (IntervalExpr.neg (normalizedLagExpression {n})).strictNegative thirteenBox=true := by kernel_decide

'''
    slacks+='''theorem thirteen_finite_signs : ThirteenFiniteSigns := by
  refine ⟨thirteen_min_nonneg_of_check thirteen_min_checked,?_⟩
  intro n
  fin_cases n
'''
    for n in range(1,13):
        slacks+=f'  · exact thirteen_lag_nonneg_of_check {n} thirteen_lag{n:02d}_checked\n'
    slacks+='\nend polyak.Certificates.PartII.Rational\n'
    path=Path(stagingRoot)/'polyak/Certificates/PartII/Rational/Slacks.lean'
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(slacks,encoding='utf-8')
    return sorted(OUTPUTS)
