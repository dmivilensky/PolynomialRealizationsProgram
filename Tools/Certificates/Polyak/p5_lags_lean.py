"""Source-linked shifted Chebyshev annotations for the P5 finite lag prefix."""
import sympy as s
from .Payload import group, polynomial
from .paths import lean_path


def _rat(q):
    q=s.Rational(q)
    return str(q.p) if q.q == 1 else f'({q.p}/{q.q})'


def _array(expr,x):
    p=s.Poly(s.expand(expr),x,domain=s.QQ)
    if p.is_zero:return 'QPoly.zero'
    return '⟨#['+','.join(_rat(p.nth(i)) for i in range(p.degree()+1))+']⟩'


def output_names():
    return ['polyak/Certificates/Continuation/P5LagCodes.lean']


def generate(root=None):
    core=group('core')['polynomials']
    x,c=s.symbols('x c')
    data={}
    text='''import polyak.Boundary.P5.LagCode
import polyak.Numerics.KernelDecide

/-! Article: (p5arc), exact Chebyshev and shifted divided coefficient proposals.
Every base array satisfies the independent Chebyshev recurrence, and every shift
and exact division is checked separately by the Lean kernel. -/
noncomputable section
namespace polyak.Certificates.Continuation.P5Lags
open LeanCert.Engine Polynomial Boundary.P5
open Boundary.P2 Numerics

'''
    for fam in ('T','U'):
        for n in range(24):
            record=core[f'{fam}{n}']
            if record['variables'] != ['c']:
                raise ValueError('unexpected P5 Chebyshev variable order')
            expr=polynomial(record)
            data[fam,n]=expr
            code=(('QPoly.constant 1' if n==0 else 'QPoly.X') if fam=='T' else
                  ('QPoly.constant 1' if n==0 else '(QPoly.constant 2).mul QPoly.X')) if n<2 else _array(expr,c)
            text+=f'def {fam}{n:02d} : QPoly := {code}\n\n'
            target=f'Spectral.cheb{fam} {n} x'
            if n<2:
                base_simp = ('QPoly.toPoly_constant' if n==0 else ('QPoly.toPoly_X' if fam=='T' else 'QPoly.toPoly_constant,QPoly.toPoly_X,QPoly.toPoly_mul'))
                text+=f'''theorem {fam}{n:02d}_exact (x : ℝ) : aeval x {fam}{n:02d}.toPoly={target} := by
  simp [{fam}{n:02d},{base_simp},Spectral.cheb{fam}]

'''
            else:
                recur='Spiral.chebT_recurrence' if fam=='T' else 'Boundary.P5.chebU_recurrence'
                text+=f'''private theorem {fam}{n:02d}_checked : polynomialCheck {fam}{n:02d}
    (((QPoly.constant 2).mul QPoly.X).mul {fam}{n-1:02d} |>.add ((QPoly.constant (-1)).mul {fam}{n-2:02d}))=true := by kernel_decide

theorem {fam}{n:02d}_exact (x : ℝ) : aeval x {fam}{n:02d}.toPoly={target} := by
  have he := congrArg (aeval x) (polynomialCheck_sound {fam}{n:02d}_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,{fam}{n-1:02d}_exact,{fam}{n-2:02d}_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := {recur} x {n-2}
  change Spectral.cheb{fam} {n} x=2*x*Spectral.cheb{fam} {n-1} x-Spectral.cheb{fam} {n-2} x at hr
  rw [hr]
  linear_combination he

'''
    for n in range(24):
        m=max(0,n-1)
        T=data['T',n];U=data['U',m]
        t0=T.subs(c,-s.Rational(1,2));u0=U.subs(c,-s.Rational(1,2))
        quots=[('TG',s.cancel((T.subs(c,1+x)-1)/x),'T',n,s.S.One,s.S.One),
               ('TX',s.cancel((T.subs(c,-s.Rational(1,2)+x)-t0)/x),'T',n,-s.Rational(1,2),t0),
               ('UX',s.cancel((U.subs(c,-s.Rational(1,2)+x)-u0)/x),'U',m,-s.Rational(1,2),u0)]
        for kind,q,fam,index,a,b in quots:
            text+=f'''def {kind}{n:02d} : QPoly := {_array(q,x)}
private theorem {kind}{n:02d}_checked : polynomialCheck
    ({fam}{index:02d}.compose ((QPoly.constant ({_rat(a)})).add QPoly.X))
    ((QPoly.constant ({_rat(b)})).add (QPoly.X.mul {kind}{n:02d}))=true := by kernel_decide

'''
        text+=f'''def UG{n:02d} : QPoly := {_array(U.subs(c,1+x),x)}
private theorem UG{n:02d}_checked : polynomialCheck
    (U{m:02d}.compose ((QPoly.constant 1).add QPoly.X)) UG{n:02d}=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag{n:02d} : LagCode {n} where
  tCentre := {_rat(t0)}
  uCentre := {_rat(u0)}
  TGdiv := TG{n:02d}
  TXdiv := TX{n:02d}
  UXdiv := UX{n:02d}
  UG := UG{n:02d}
  TY := T{n:02d}
  UY := U{m:02d}
  TG_exact h := by simpa using shifted_divided_exact T{n:02d} T{n:02d}_exact 1 1 TG{n:02d} TG{n:02d}_checked h
  TX_exact r := by simpa using shifted_divided_exact T{n:02d} T{n:02d}_exact (-1/2) ({_rat(t0)}) TX{n:02d} TX{n:02d}_checked r
  UX_exact r := by simpa using shifted_divided_exact U{m:02d} U{m:02d}_exact (-1/2) ({_rat(u0)}) UX{n:02d} UX{n:02d}_checked r
  UG_exact h := by simpa using shifted_exact U{m:02d} U{m:02d}_exact 1 UG{n:02d} UG{n:02d}_checked h
  TY_exact := T{n:02d}_exact
  UY_exact := U{m:02d}_exact

'''
    text+='def codes : (n : Fin 24) → LagCode n\n'
    text+=''.join(f'  | ⟨{n},_⟩ => lag{n:02d}\n' for n in range(24))
    text+='  | ⟨n+24,h⟩ => False.elim (by omega)\n'
    text+='\nend polyak.Certificates.Continuation.P5Lags\n'
    p=lean_path(root,output_names()[0]);p.write_text(text,encoding='utf-8')
    return output_names()
