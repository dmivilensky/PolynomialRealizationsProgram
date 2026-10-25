"""Exact tensor Bernstein proposals for the fixed P1 lag source.

Read only archived Chebyshev coefficients.  The source recurrence and every
polynomial identity are independently checked in Lean; coefficient signs and
this transformation are not mathematical premises.
"""
import sympy as s
from .Payload import group, polynomial
from .paths import lean_path


def _rat(q):
    q=s.Rational(q)
    return str(q.p) if q.q == 1 else f'({q.p}/{q.q})'


def output_names():
    return [f'polyak/Certificates/P1Slacks/Lag{n:02d}{"Lower" if sign == -1 else "Upper"}.lean'
            for n in range(1,13) for sign in (-1,1)
            if (n,sign) not in ((1,-1),(2,1),(3,1))]


def generate(root=None):
    core=group('core')['polynomials']
    z,a,x,y=s.symbols('z a x y')

    def cheb(family,n,value):
        record=core[f'{family}{n}']
        if record['variables'] != ['c']:
            raise ValueError('unexpected P1 Chebyshev variable order')
        return polynomial(record).subs(s.Symbol('c'),value)

    D=2+z*a+z*z*(a*a-1)
    E=1+z*a+z*z*(2*a*a-1)
    paths=[]
    for n in range(1,13):
        for sign in (-1,1):
            if (n,sign) in ((1,-1),(2,1),(3,1)):
                continue
            raw=s.cancel(z**(n-1)*(z*(1+z*a)*(cheb('T',n,1/z)-cheb('T',n,a))
                           +sign*D*cheb('U',n-1,a)-sign*E*cheb('U',n-1,1/z)))
            if sign == 1 and n >= 4:
                raw=s.cancel(raw/z**2)
            p=s.Poly(s.expand(raw.subs(a,-y*z/2).subs(z,s.Rational(3,4)*x)),x,y)
            d,e=p.degree(x),p.degree(y)
            coefficients=[]
            for i in range(d+1):
                row=[]
                for j in range(e+1):
                    # Binomial factors are incorporated in the certificate's basis.
                    row.append(sum(v*s.binomial(i,k)*s.binomial(j,l)
                                   /s.binomial(d,k)/s.binomial(e,l)
                                   for (k,l),v in p.terms() if k<=i and l<=j)
                               *s.binomial(d,i)*s.binomial(e,j))
                coefficients.append(row)
            suffix=f'{n:02d}{"Lower" if sign == -1 else "Upper"}'
            matrix='![\n'+',\n'.join('    !['+','.join(_rat(q) for q in row)+']'
                                      for row in coefficients)+']'
            row_text=''
            row_names=[]
            for i,row in enumerate(coefficients):
                rp=s.Poly(s.expand(sum(q*y**j*(1-y)**(e-j) for j,q in enumerate(row))),y)
                expression='(.literal 0)'
                for k in range(max(0,rp.degree()),-1,-1):
                    expression=f'(.add (.literal ({_rat(rp.nth(k))})) (.mul .y {expression}))'
                rowname=f'row{suffix}_{i:02d}'
                row_names.append(rowname)
                row_text+=f'''/-- Exact reduced polynomial annotation for tensor row {i}. -/
private def {rowname} : Expr := {expression}

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked{suffix}_{i:02d} :
    (certificate{suffix}.rowExpression ⟨{i},by decide⟩).check {rowname}=true := by kernel_decide

'''
            row_text+=f'def rows{suffix} : Fin (certificate{suffix}.degree0+1) → Expr := !['+','.join(row_names)+']\n\n'
            row_text+=f'theorem rowsChecked{suffix} : ∀ i, (certificate{suffix}.rowExpression i).check (rows{suffix} i)=true := by\n  intro i\n  fin_cases i\n'
            row_text+=''.join(f'  · exact checked{suffix}_{i:02d}\n' for i in range(d+1))+'\n'
            text=f'''import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag {n}, sign {sign}.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate{suffix} : Certificate where
  degree0 := {d}
  degree1 := {e}
  coefficient := {matrix}

{row_text}
/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity{suffix} : slackRowsIdentityCheck {n} ({sign}) certificate{suffix} rows{suffix}=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted{suffix} : certificate{suffix}.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive{suffix} {{z a : ℝ}} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack {n} ({sign}) z a :=
  by simpa using scaledSlack_pos_of_rows certificate{suffix} rows{suffix} rowsChecked{suffix} identity{suffix} accepted{suffix} hz hz1 ha

end polyak.Certificates.P1Slacks
'''
            relative=f'polyak/Certificates/P1Slacks/Lag{suffix}.lean'
            path=lean_path(root,relative)
            path.write_text(text,encoding='utf-8')
            paths.append(relative)
    return paths
