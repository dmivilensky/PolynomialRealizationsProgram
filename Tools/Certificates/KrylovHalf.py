#!/usr/bin/env python3
"""Propose the reproducible rational half-gamma differential barriers.

Article: main_krylov, apC:prop:digits (agreed five-significant-digit variant).
Uses only Python's standard library. Decimal saddle-series evaluations and
polynomial interpolation suggest coefficients; exact Fraction arithmetic then
proposes Bernstein coefficients. None of these computations is trusted.
The generated HalfBarrierWitness.lean proves the derivative and residual
identities by ring normalization and the signs by positivity in Lean's kernel.

Run with no arguments to check reproducibility, or --write to regenerate.
The proposal script is separate from verification and never writes .olean files.
"""
from decimal import Decimal as D,getcontext
from fractions import Fraction as F
from math import comb
getcontext().prec=90

def add(a,b):
 c=[a[0]*0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return c

def scale(a,k):return [x*k for x in a]
def mul(a,b):
 c=[a[0]*0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def res(p):
 z=p[0]*0;o=z+1
 dp=[(i+1)*p[i] for i in range(len(p))]
 return add(mul(mul([4*o,-o],dp),add([o],scale(p,-1))),scale(mul(add([3*o],scale([z]+p,-1)),add([o],scale(p,-2))),-1))

def bern(p,L=F(3)):
 n=len(p)-1
 return [sum(p[j]*L**j*F(comb(i,j),comb(n,j)) for j in range(i+1)) for i in range(n+1)]

p=[(D(5)-D(13).sqrt())/4]
for k in range(1,51):
 q=p+[D(0)]
 a=res(q)[k]
 q[-1]=1
 b=res(q)[k]-a
 p.append(-a/b)

def interp(xs,ys):
 d=ys.copy(); r=[D(0)]; prod=[D(1)]
 for k in range(len(xs)):
  r=add(r,scale(prod,d[0]))
  d=[(d[i+1]-d[i])/(xs[i+k+1]-xs[i]) for i in range(len(d)-1)]
  prod=mul(prod,[-xs[k],D(1)])
 return r

from pathlib import Path
n=16
xs=[D(3)*i/n for i in range(n+1)]
ys=[sum(a*x**i if i else a for i,a in enumerate(p)) for x in xs]
pp=interp(xs,ys)
q=[F(str(x.quantize(D('1e-20')))) for x in pp]
def rat(x):return str(x.numerator) if x.denominator==1 else f'({x.numerator} / {x.denominator})'
def term(c,i,var):return f'{rat(c)} * {var} ^ {i}'
def poly(cs,var):return ' +\n    '.join(term(c,i,var) for i,c in enumerate(cs))
def bernraw(p):
 b=bern(p);N=len(p)-1
 return [b[i]*F(comb(N,i),3**N) for i in range(N+1)]
out='''import krylov.LotkaVolterra.HalfCoarseBound

/-!
Article: main_krylov, apC:prop:digits, reduced-precision half-gamma certificate.
The witnesses are literal rational polynomials. Their residual identities are
checked by ring normalization, and the Bernstein representation proves the
required strict signs throughout the whole graph interval. External arithmetic
only proposes the coefficients: none of its output is a premise of a theorem.
Source: polynomial differential barriers and the classical Bernstein basis.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
set_option maxHeartbeats 4000000

/-- Central rational approximation in the distance v=4-U from the saddle. -/
def halfCertifiedP (v : ℝ) : ℝ :=
    '''+poly(q,'v')+'''

/-- Its literal derivative. -/
def halfCertifiedPDerivative (v : ℝ) : ℝ :=
    '''+poly([q[i+1]*(i+1) for i in range(n)],'v')+'''

/-- Exact differentiation of the rational witness polynomial. -/
theorem halfCertifiedP_hasDerivAt (v : ℝ) :
    HasDerivAt halfCertifiedP (halfCertifiedPDerivative v) v := by
'''+ ''.join(f'  have h{i} := '+(f'((hasDerivAt_id v).pow {i}).const_mul {rat(q[i])}' if i==0 else f'h{i-1}.add (((hasDerivAt_id v).pow {i}).const_mul {rat(q[i])})')+'\n' for i in range(n+1))+f'''  convert h{n} using 1\n  · rfl\n  · norm_num [halfCertifiedPDerivative]\n    ring\n'''+'''
/-- Upper and lower witnesses, encoded by sign=1 and sign=-1 respectively. -/
def halfCertifiedBarrier (sign U : ℝ) : ℝ :=
  3 - (4-U) * (halfCertifiedP (4-U) - sign / 10000000)

/-- Literal derivative of the signed witness. -/
def halfCertifiedBarrierDerivative (sign U : ℝ) : ℝ :=
  halfCertifiedP (4-U) - sign / 10000000 + (4-U) * halfCertifiedPDerivative (4-U)

/-- Exact derivative of each numerical barrier. -/
theorem halfCertifiedBarrier_hasDerivAt (sign U : ℝ) :
    HasDerivAt (halfCertifiedBarrier sign) (halfCertifiedBarrierDerivative sign U) U := by
  have hv := (hasDerivAt_id U).const_sub 4
  have hp := ((halfCertifiedP_hasDerivAt (4-U)).comp U hv).sub_const (sign / 10000000)
  convert (hv.mul hp).const_sub 3 using 1
  · rfl
  · dsimp [halfCertifiedBarrierDerivative]
    ring

@[simp] theorem halfCertifiedBarrier_four (sign : ℝ) : halfCertifiedBarrier sign 4 = 3 := by
  simp [halfCertifiedBarrier]

'''
for sign in [-1,1]:
 qq=q.copy();qq[0]-=F(sign,10000000)
 rr=scale(res(qq),-sign)
 coeff=bernraw(rr)
 assert min(coeff)>0
 P=' +\n    '.join(f'{rat(c)} * v ^ {i} * (3-v) ^ {len(coeff)-1-i}' for i,c in enumerate(coeff))
 name='upper' if sign==1 else 'lower'
 out+=f'''/-- The {name} barrier has the required exact strict LV residual sign. -/
theorem halfCertifiedBarrier_{name}_residual {{U : ℝ}} (hU : U ∈ Icc (1 : ℝ) 4)
    (hne : U < 4) :
    ({sign} : ℝ) * (U * halfCertifiedBarrierDerivative ({sign}) U *
      (halfCertifiedBarrier ({sign}) U + 1 - U) -
      2 * halfCertifiedBarrier ({sign}) U * (halfCertifiedBarrier ({sign}) U - 1 - U/2)) < 0 := by
  let v := 4-U
  have hv : 0 < v := by dsimp [v]; linarith
  have h3 : 0 ≤ 3-v := by dsimp [v]; linarith [hU.1]
  let Q : ℝ :=
    {P}
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have he : ({sign} : ℝ) * (U * halfCertifiedBarrierDerivative ({sign}) U *
      (halfCertifiedBarrier ({sign}) U + 1 - U) -
      2 * halfCertifiedBarrier ({sign}) U * (halfCertifiedBarrier ({sign}) U - 1 - U/2)) = -v*Q := by
    dsimp [halfCertifiedBarrier, halfCertifiedBarrierDerivative,
      halfCertifiedP, halfCertifiedPDerivative, Q, v]
    ring
  rw [he]
  simpa only [neg_mul] using neg_neg_of_pos (mul_pos hv hQ)

'''
out+='end\nend krylov.LotkaVolterra\n'
import argparse
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--write", action="store_true", help="Rewrite the proposed Lean witnesses")
args = parser.parse_args()
path = Path(__file__).resolve().parents[2] / "krylov/Numerics/HalfBarrierWitness.lean"
if args.write:
    path.write_text(out)
    print(f"Wrote {path}")
else:
    if path.read_text() != out:
        raise SystemExit("Witness mismatch; inspect the proposal before invoking --write")
    print("Half-gamma rational witnesses reproduce exactly. Mathematical validation is by Lean.")
