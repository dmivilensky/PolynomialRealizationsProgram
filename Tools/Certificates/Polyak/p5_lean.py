"""Propose exact source-linked P5 coefficient tables for Lean checking.

Only mathematical data and proof text are emitted.  The independently defined
Chebyshev system, its semantic identities, the quintic root and all analytic
proofs remain Lean sources.  Python and SymPy are outside the trust boundary.
"""
from pathlib import Path
from fractions import Fraction
import sympy as s
from .Payload import group
from .paths import lean_root


def source_polynomials():
    """Check the variable order before reading archived exponents positionally."""
    polynomials = group('p5').get('polynomials')
    if not isinstance(polynomials, dict):
        raise ValueError('missing P5 polynomial table')
    unknowns = ['A', 'B', 'y', 'P', 'D', 'w2', 'w3']
    orders = {f'F{i}': ['h', *unknowns] for i in range(7)}
    orders.update({f'F0_{i}': unknowns for i in range(7)})
    univariate = [f'critical_{name}' for name in ('A', 'B', 'D', 'P', 'w2', 'w3', 'w5')]
    univariate += [f'dual_quotient_q{i}' for i in range(3)]
    for block, dimension in (('primal', 4), ('dual', 3)):
        univariate.append(f'{block}_jacobian_det')
        univariate.extend(f'{block}_jacobian_{i}_{j}'
                          for i in range(dimension) for j in range(dimension))
    orders.update({name: ['y'] for name in univariate})
    for name, expected in orders.items():
        record = polynomials.get(name)
        if not isinstance(record, dict) or record.get('variables') != expected:
            raise ValueError('unexpected P5 polynomial variable order: ' + name)
    return polynomials


def generate_system(p):
    def rat(a):
     a=Fraction(a)
     return str(a.numerator) if a.denominator==1 else f'({a.numerator}/{a.denominator})'
    def term(a,es):
     parts=[f'MvPolynomial.C ({rat(a)} : ℚ)']
     for i,e in enumerate(es):
      if e:parts.append(f'MvPolynomial.X ({i} : Fin 8)'+('' if e==1 else f'^{e}'))
     return '*'.join(parts)
    s='''import polyak.Boundary.P5.SourceChebyshev

/-!
Article: (blowup), exact finite coefficient certificates for the actual
regularized P₅ equations.  Every array is related by a checked polynomial
identity to the separately defined Chebyshev source system.
-/
noncomputable section
namespace polyak.Certificates.P5
open Boundary.P5

'''
    for i in range(7):
     terms=p['F'+str(i)]['terms']
     chunks=[terms[k:k+12] for k in range(0,len(terms),12)]
     for j,ts in enumerate(chunks):
      s+=f'/-- Article: coefficient block {j} of regularized equation {i}. -/\ndef F{i}Part{j} : SourcePolynomial :=\n  '+ '+\n  '.join(term(a,es) for a,es in ts)+'\n\n'
     s+=f'/-- Article: exact coefficients of regularized equation {i}. -/\ndef F{i} : SourcePolynomial := '+ '+'.join(f'F{i}Part{j}' for j in range(len(chunks)))+'\n\n'
    for i,(m,sg,sc) in enumerate([(1,-1,1),(2,1,2),(3,1,4),(5,1,4)]):
     parts=','.join(f'F{i}Part{j}' for j in range((len(p['F'+str(i)]['terms'])+11)//12))
     s+=f'''/-- Article: exact division by h of the {m}-lag primal equation at all real data. -/
theorem primal_division_{i} (z : Fin 8 → ℝ) :
    sourceEval z H*sourceEval z F{i} = {sc}*sourceEval z (primalNumerator {m} ({sg})) := by
  norm_num [sourceEval,F{i},{parts},primalNumerator,sourceRaw,
    H,U,X,Y,Probability,Charge,G,sourceVar]
  ring

'''
    for i in range(3):
     k=i+4
     parts=','.join(f'F{k}Part{j}' for j in range((len(p['F'+str(k)]['terms'])+11)//12))
     s+=f'''/-- Article: the regularized dual equation is the actual cleared source equation. -/
theorem dual_source_{i} (z : Fin 8 → ℝ) : sourceEval z F{k} = sourceEval z (dualNumerator {i}) := by
'''
     if i==0:
      s+=f'''  norm_num [sourceEval,F{k},{parts},dualNumerator,dualSource,dualDenominator,
    H,U,X,Y,W₂,W₃,W₅,G,sourceVar]
  ring

'''
     else:
      atom='X' if i==1 else 'Y'
      s+=f'''  change sourceEval z F{k}=sourceEval z (dualSource.derivative.eval {atom})
  rw [dualSource_derivative]
  norm_num [sourceEval,F{k},{parts},dualDerivativeSource,dualDenominator,
    H,U,X,Y,W₂,W₃,W₅,G,sourceVar]
  ring

'''
    s+='end polyak.Certificates.P5\n'
    return s


def generate_critical(p):
    keys={'A':'critical_A','B':'critical_B','D':'critical_D','P':'critical_P','w2':'critical_w2','w3':'critical_w3','w5':'critical_w5','dualDet':'dual_jacobian_det','primalDet':'primal_jacobian_det','q0':'dual_quotient_q0','q1':'dual_quotient_q1','q2':'dual_quotient_q2'}
    def rat(a):
     a=Fraction(a)
     return str(a.numerator) if a.denominator==1 else f'({a.numerator}/{a.denominator})'
    def coeffs(key):
     ts=p[key]['terms'];d=max(e[0] for a,e in ts);c=[Fraction(0)]*(d+1)
     for a,e in ts:c[e[0]]=Fraction(a)
     if key.startswith('dual_quotient'):c=[a/15 for a in c]
     return c
    def poly(c):return '+'.join(f'C ({rat(a)} : ℚ)'+('' if i==0 else '*X' if i==1 else f'*X^{i}') for i,a in enumerate(c) if a)
    def horn(c):
     v='0'
     for a in reversed(c):v=f'C ({rat(a)} : ℚ)+X*({v})'
     return v
    s='''import polyak.Boundary.P5.CriticalData
import polyak.Numerics.Modular

/-!
Article: exact coefficient certificates for P₅ at h=0.
Use: finite rational arrays are linked to the independent critical source
formulas before any sign or algebraic conclusion is drawn.
-/
noncomputable section
open scoped Polynomial
namespace polyak.Certificates.P5
open Polynomial Numerics Boundary.P5 LeanCert.Engine
'''
    for n,k in keys.items():
     c=coeffs(k)
     s+=f'''\n/-- Article: exact executable coefficients for {n} at criticality. -/
def {n}Code : PolynomialCode {n}Polynomial where
  code := ⟨#[{','.join(rat(a) for a in c)}]⟩
  exact := by
    change {horn(c)} = {n}Polynomial
    dsimp only [{n}Polynomial]
    ring
'''
    s+='\nend polyak.Certificates.P5\n'
    return s


def generate_critical_system(p):
    def rat(a):
     a=Fraction(a);return str(a.numerator) if a.denominator==1 else f'({a.numerator}/{a.denominator})'
    def term(a,es,n=7):
     parts=[f'MvPolynomial.C ({rat(a)} : ℚ)']
     for i,e in enumerate(es):
      if e:parts.append(f'MvPolynomial.X ({i} : Fin {n})'+('' if e==1 else f'^{e}'))
     return '*'.join(parts)
    s='''import polyak.Boundary.P5.System
import polyak.Boundary.P5.Differential

/-!
Article: Theorem p5h0, the exact decoupled system at h=0.
Use: the low-degree critical equations are proved equal to the actual
regularized system at zero, before their Jacobian or solution is used.
-/
noncomputable section
namespace polyak.Boundary.P5
open Certificates.P5

'''
    for i in range(7):
     ts=p['F0_'+str(i)]['terms'];chunks=[ts[k:k+12] for k in range(0,len(ts),12)]
     for j,terms in enumerate(chunks):
      s+=f'/-- Article: exact critical source coefficient block {j} in equation {i}. -/\ndef C{i}Part{j} : MvPolynomial (Fin 7) ℚ :=\n  '+ '+\n  '.join(term(a,es) for a,es in terms)+'\n\n'
     s+=f'/-- Article: critical equation {i} as a polynomial in the seven unknowns. -/\ndef C{i} : MvPolynomial (Fin 7) ℚ := '+ '+'.join(f'C{i}Part{j}' for j in range(len(chunks)))+'\n\n'
    s+='''/-- Article: the seven critical source polynomials, in the original equation order. -/
def criticalSource : Fin 7 → MvPolynomial (Fin 7) ℚ := ![C0,C1,C2,C3,C4,C5,C6]

'''
    for i in range(7):
     s+=f'/-- Article: critical polynomial in equation slot {i}. -/\n@[simp] theorem criticalSource_{i} : criticalSource {i}=C{i} := rfl\n\n'
    for i in range(7):
     parts=','.join(f'F{i}Part{j}' for j in range((len(p['F'+str(i)]['terms'])+11)//12))
     cparts=','.join(f'C{i}Part{j}' for j in range((len(p['F0_'+str(i)]['terms'])+11)//12))
     s+=f'''/-- Article: exact specialization of the actual regularized equation {i} at h=0. -/
theorem regularSystem_zero_{i} (Z : Coordinates) : regularSystem (0,Z) {i}=polynomialValue C{i} Z := by
  norm_num [regularSystem,sourceEval,regularizedPolynomial_{i},F{i},{parts},
    polynomialValue,C{i},{cparts}]

'''
    s+='''/-- Article: the entire actual h=0 system is the explicit decoupled critical system. -/
theorem regularSystem_zero (Z : Coordinates) :
    regularSystem (0,Z)=(fun i => polynomialValue (criticalSource i) Z) := by
  ext i
  fin_cases i
'''
    for i in range(7):s+=f'  · exact regularSystem_zero_{i} Z\n'
    s+='\nend polyak.Boundary.P5\n';
    return s


def generate_jacobian(p):
    vs=s.symbols('A B y P D w2 w3');y=vs[2]
    q=32*y**5-40*y**4+16*y**3-6*y*y-12*y+3
    values={v:sum(s.Rational(a)*y**ns[0] for a,ns in p['critical_'+str(v)]['terms']) for v in vs if v!=y}
    def exprdata(name):return sum(s.Rational(a)*y**ns[0] for a,ns in p[name]['terms'])
    def f0(i):return sum(s.Rational(a)*s.prod(v**n for v,n in zip(vs,ns)) for a,ns in p['F0_'+str(i)]['terms'])
    def rat(a):
     a=Fraction(str(a));return str(a.numerator) if a.denominator==1 else f'({a.numerator}/{a.denominator})'
    def leanpoly(e):return '+'.join(f'Polynomial.C ({rat(a)} : ℚ)'+('' if ns[0]==0 else '*Polynomial.X' if ns[0]==1 else f'*Polynomial.X^{ns[0]}') for ns,a in reversed(s.Poly(e,y).terms())) or '0'
    def leanreal(e):return str(e).replace('**','^').replace('y','y₀')
    rows={'primal':list(range(4)),'dual':[4,5,6]};cols={'primal':[0,1,4,3],'dual':[2,5,6]}
    out='''import polyak.Boundary.P5.CriticalSystem

/-!
Article: Theorem p5h0, the two genuine critical Jacobian blocks.
Use: all entries are the actual formal partial derivatives of the h=0 system;
exact identities in ℚ(y₀) identify their finite algebraic representations.
-/
noncomputable section
open scoped Polynomial
namespace polyak.Boundary.P5

/-- Article: the actual critical Jacobian, before any coefficient representation. -/
def criticalJacobian : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => polynomialValue (MvPolynomial.pderiv j (criticalSource i)) criticalPoint

'''
    for name in ['primal','dual']:
     for i,row in enumerate(rows[name]):
      cparts=','.join(f'C{row}Part{j}' for j in range((len(p['F0_'+str(row)]['terms'])+11)//12))
      for j,col in enumerate(cols[name]):
       expected=exprdata(f'{name}_jacobian_{i}_{j}')
       actual=s.diff(f0(row),vs[col]).subs(values,simultaneous=True)
       quotient,rem=s.div(s.expand(actual-expected),q,y);assert rem==0,(name,i,j,rem)
       ident=f'{name}Entry{i}{j}'
       out+=f'''/-- Article: exact algebraic representation of critical {name} block entry ({i},{j}). -/
def {ident} : ℚ[X] := {leanpoly(expected)}

/-- Article: the proposed entry equals the actual critical partial derivative. -/
theorem {name}_entry_{i}_{j} : criticalJacobian {row} {col}=Polynomial.aeval y₀ {ident} := by
  norm_num [criticalJacobian,criticalSource_{row},C{row},{cparts},polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply,
    w2₀,w3₀,w2Polynomial,w3Polynomial,{ident}]
'''
       if quotient==0:
        out+='\n'
       else:out+=f'  linear_combination ({leanreal(quotient)}) * y₀_equation\n\n'
    for row in [4,5,6]:
     cparts=','.join(f'C{row}Part{j}' for j in range((len(p['F0_'+str(row)]['terms'])+11)//12))
     for col in [0,1,4,3]:
      out+=f'''/-- Article: the dual critical equations do not depend on any primal unknown. -/
theorem lower_left_{row}_{col} : criticalJacobian {row} {col}=0 := by
  norm_num [criticalJacobian,criticalSource_{row},C{row},{cparts},polynomialValue,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,Pi.single_apply]

'''
    out+='end polyak.Boundary.P5\n';
    return out


def generate_matrix(p):
    y=s.symbols('y');q=32*y**5-40*y**4+16*y**3-6*y*y-12*y+3
    rows={'primal':list(range(4)),'dual':[4,5,6]};cols={'primal':[0,1,4,3],'dual':[2,5,6]}
    def matrixlit(entries):return '!!['+'; '.join(', '.join(row) for row in entries)+']'
    def ex(k):return sum(s.Rational(a)*y**ns[0] for a,ns in p[k]['terms'])
    sr='''import polyak.Boundary.P5.CriticalJacobian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
Article: Theorem p5h0, exact nonsingularity of both critical Jacobian blocks.
Use: these are submatrices of the actual Frechet Jacobian, rather than
independent invertibility data supplied to the implicit function theorem.
-/
noncomputable section
namespace polyak.Boundary.P5
'''
    for name,n in [('primal',4),('dual',3)]:
     entries=[[f'criticalJacobian {rows[name][i]} {cols[name][j]}' for j in range(n)] for i in range(n)]
     reprs=[[f'Polynomial.aeval y₀ {name}Entry{i}{j}' for j in range(n)] for i in range(n)]
     sr+=f'''\n/-- Article: the actual {name} block in the source unknown order. -/
def {name}Matrix : Matrix (Fin {n}) (Fin {n}) ℝ := {matrixlit(entries)}

/-- Article: every entry of the block has its checked algebraic representation. -/
theorem {name}Matrix_repr : {name}Matrix={matrixlit(reprs)} := by
  ext i j
  fin_cases i <;> fin_cases j
'''
     for i in range(n):
      for j in range(n):sr+=f'  · exact {name}_entry_{i}_{j}\n'
     M=s.Matrix(n,n,lambda i,j:ex(f'{name}_jacobian_{i}_{j}'))
     quotient,rem=s.div(s.expand(M.det()-ex(name+'_jacobian_det')),q,y);assert rem==0
     defs=','.join(f'{name}Entry{i}{j}' for i in range(n) for j in range(n))
     sr+=f'''\n/-- Article: the genuine {name} block determinant equals the specified element of ℚ(y₀). -/
theorem {name}Matrix_det : {name}Matrix.det={name}Det₀ := by
  rw [{name}Matrix_repr]
'''
     if n==4:sr+='  rw [Matrix.det_succ_row_zero]\n'
     sr+=f'''  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,Matrix.submatrix_apply,Fin.succAbove,
    {defs},{name}Det₀,{name}DetPolynomial]
'''
     if quotient==0:sr+='  ring\n'
     else:sr+='  linear_combination ('+str(quotient).replace('**','^').replace('y','y₀')+') * y₀_equation\n'
     sr+=f'''\n/-- Article: no singularity in the actual {name} critical Jacobian block. -/
theorem {name}Matrix_det_ne_zero : {name}Matrix.det ≠ 0 := by
  rw [{name}Matrix_det]
  exact critical_block_determinants_ne_zero.{2 if name=='primal' else 1}
'''
    sr+='\nend polyak.Boundary.P5\n';
    return sr


def generate_all(root=None):
    """Regenerate all finite P5 source coefficient proposals and their Lean identities."""
    root=lean_root(root)
    polynomials=source_polynomials()
    outputs={
        'polyak/Certificates/P5System.lean':generate_system(polynomials),
        'polyak/Certificates/P5Critical.lean':generate_critical(polynomials),
        'polyak/Boundary/P5/CriticalSystem.lean':generate_critical_system(polynomials),
        'polyak/Boundary/P5/CriticalJacobian.lean':generate_jacobian(polynomials),
        'polyak/Boundary/P5/CriticalMatrix.lean':generate_matrix(polynomials),
    }
    for filename,contents in outputs.items():
        target=root/filename
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(contents,encoding='utf-8')
        print(target,flush=True)
    return list(outputs)


if __name__=='__main__':
    generate_all()
