"""Propose source-linked exact rational code for Lean. No proof is trusted here."""
from pathlib import Path
from functools import reduce
import sympy as s
from . import p2
from .paths import lean_root, lean_path


def rat(q):
    q=s.Rational(q)
    return str(q.p) if q.q==1 else f"({q.p}/{q.q})"

def arr(p,z):
    p=s.Poly(p,z,domain=s.QQ)
    return '⟨#['+','.join(rat(p.nth(k)) for k in range(max(0,p.degree())+1))+']⟩' if not p.is_zero else 'QPoly.zero'

class Builder:
    def __init__(self,z):
        self.z=z; self.lines=[]; self.cache={}; self.count=0; self.sub={}
        self.srcdefs=[]; self.den_cache={}
    def new(self,expr,op,source,raw):
        expr=s.cancel(expr); n,d=s.fraction(expr)
        name=f'node{self.count}'; self.count+=1
        sr=f'formula{self.count}'
        key=tuple(s.Poly(d,self.z).all_coeffs())
        oldden=self.den_cache.get(key)
        self.den_cache[key]=name+'Denominator' if oldden is None else oldden
        denproof=f'  {oldden}' if oldden else f'  signedPolynomialCheck_ne_zero (sg := {s.sign(d.subs(self.z,s.Rational(6789,4000)))}) (by kernel_decide)'
        self.lines += [f'/-- Article: exact source arithmetic node {self.count}. -/',
                       f'private def {sr} (z : ℝ) : ℝ := {source}',
                       f'private theorem {name}Denominator : ∀ z∈parameterInterval, aeval z ({arr(d,self.z)} : QPoly).toPoly≠0 :=',
                       denproof,
                       f'private theorem {name}Cross : polynomialCheck',
                       f'    (({raw[0]} : QPoly).mul {arr(d,self.z)})',
                       f'    (({arr(n,self.z)} : QPoly).mul ({raw[1]}))=true := by kernel_decide',
                       f'private def {name} : RationalCode parameterInterval {sr} :=',op,
                       f'  |>.recode {arr(n,self.z)} {arr(d,self.z)} {name}Denominator {name}Cross','']
        self.srcdefs.append(sr)
        return (name,sr,expr,n,d)
    def code(self,expr):
        if expr in self.cache:return self.cache[expr]
        if expr in self.sub:return self.sub[expr]
        if expr==self.z:
            ans=('(RationalCode.variable parameterInterval)','id',expr,self.z,s.S.One)
        elif expr.is_Rational:
            q=rat(expr)
            ans=(f'(RationalCode.constant parameterInterval ({q}))',f'(fun _ : ℝ => (({q} : ℚ) : ℝ))',expr,expr,s.S.One)
        elif expr.is_Add or expr.is_Mul:
            op='add' if expr.is_Add else 'mul'; symbol='+' if op=='add' else '*'
            args=list(expr.args); a=self.code(args[0]); acc=args[0]
            for e in args[1:]:
                b=self.code(e); acc=(acc+e) if op=='add' else (acc*e)
                an,ad,bn,bd=[f'({arr(q,self.z)} : QPoly)' for q in [a[3],a[4],b[3],b[4]]]
                raw=(f'({an}.mul {bd}).add ({bn}.mul {ad})',f'{ad}.mul {bd}') if op=='add' else (f'{an}.mul {bn}',f'{ad}.mul {bd}')
                a=self.new(a[2]+b[2] if op=='add' else a[2]*b[2],
                           f'  ({a[0]}.{op} {b[0]})',f'({a[1]} z){symbol}({b[1]} z)',raw)
            ans=a
        elif expr.is_Pow and expr.exp.is_Integer:
            a=self.code(expr.base); power=int(expr.exp)
            if power>=0:
                ans=self.new(a[2]**power,f'  ({a[0]}.pow {power})',f'({a[1]} z)^{power}',(f'polynomialPower {arr(a[3],self.z)} {power}',f'polynomialPower {arr(a[4],self.z)} {power}'))
            else:
                sign=s.sign(a[3].subs(self.z,s.Rational(6789,4000)))
                ans=self.new(1/a[2],f'  ({a[0]}.inv (signedPolynomialCheck_ne_zero (sg := {sign}) (by kernel_decide)))',f'({a[1]} z)⁻¹',(arr(a[4],self.z),arr(a[3],self.z)))
                if power < -1:
                    ans=self.new(ans[2]**(-power),f'  ({ans[0]}.pow {-power})',f'({ans[1]} z)^{(-power)}',(f'polynomialPower {arr(ans[3],self.z)} {-power}',f'polynomialPower {arr(ans[4],self.z)} {-power}'))
        else:raise ValueError(expr)
        self.cache[expr]=ans
        return ans
    def alias(self,expr,name,actual,unfold,moment_index=None):
        expr=s.factor_terms(expr)
        a=self.code(expr)
        defs=','.join(self.srcdefs+unfold)
        self.lines += [f'/-- Article: exact coefficient representation of the independently specified {name} source. -/',
                       f'def {name}Code : RationalCode parameterInterval {actual} where',
                       f'  numerator := {a[0]}.numerator',f'  denominator := {a[0]}.denominator',
                       f'  denominator_ne := {a[0]}.denominator_ne',
                       f'  exact z hz := by',
                       f'    have he : {actual} z={a[1]} z := by',
                       *([f'      change moment z {moment_index}={a[1]} z', '      rw [moment]'] if moment_index is not None else []),
                       f'      try dsimp only [{defs}]',
                       '      try push_cast',
                       '      try simp_rw [div_eq_mul_inv]',
                       '      try simp_rw [mul_inv_rev]',
                       '      try simp_rw [inv_pow]',
                       '      try ring',
                       f'    exact he.trans ({a[0]}.exact z hz)','']
        alias=(name+'Code',actual,a[2],a[3],a[4])
        return alias


def generate(root=None):
    m=p2.model(False); z=m['z']; b=Builder(z)
    header='''import polyak.Numerics.KernelDecide
import polyak.Boundary.P2.Check

/-!
Article: Definition p2data, exact rational coefficient proposals.
Use: every exported RationalCode has a specified source formula, proved denominators
and local kernel-checked polynomial cross products. Generated annotations do not
supply a mathematical hypothesis. Regenerate with certificates/p2_lean.py.
-/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
'''
    sources=[('G','G'),('u','u'),('W','W'),('a','atomA'),('b','atomB'),('mc','meanCosine'),('d','d'),('slope','slope')]
    unfold=['G','u','W','atomA','atomB','meanCosine','d','meanGap','slope','qMinus','qPlus','rMinus','rPlus','K6','F8','M10','D14','eMinus','ePlus','id_eq']
    for key,actual in sources:
        print('generating',key,flush=True)
        ans=b.alias(m[key],actual,actual,unfold)
        b.sub[s.Symbol('ACTUAL_'+key)]=ans
    UU,AA,BB,MC=[s.Symbol('ACTUAL_'+key) for key in ['u','a','b','mc']]
    b.alias(1-UU**2+AA*MC+BB,'meanGap','meanGap',unfold)
    path=lean_path(root,'polyak/Certificates/P2Codes.lean')
    path.write_text(header+'\n'.join(b.lines)+'\nend\nend polyak.Boundary.P2\n')
    print(path,b.count,flush=True)



def generate_signs(root=None):
    m=p2.model(False); z=m['z']; b=Builder(z)
    symbols={}
    for key,actual in [('G','G'),('u','u'),('W','W'),('a','atomA'),('b','atomB'),('mc','meanCosine'),('d','d'),('gap','meanGap'),('slope','slope')]:
        sym=s.Symbol('SOURCE_'+key); symbols[key]=sym
        n,den=s.fraction(s.cancel(m[key]))
        b.sub[sym]=(actual+'Code',actual,m[key],n,den)
    G,u,W,a,bb,mc,d,gap,slope=[symbols[k] for k in ['G','u','W','a','b','mc','d','gap','slope']]
    qm,rm,rp,em,ep,M10,N10=[m[k] for k in ['qm','rm','rp','em','ep','M10','N10']]
    meanfactor=32*z**3*em*ep*(z**3+2*z-4)*N10/(rm**2*rp*M10**2)
    upperfactor=(N10/M10)*(em*ep*qm**3)/(8*z*z*rp**2*rm**7)
    entries=[
        ('G_lower',G-s.Rational(10233,10000),'G z-(10233/10000)'),
        ('G_upper',s.Rational(10337,10000)-G,'(10337/10000)-G z'),
        ('u_lower',u-s.Rational(511,1000),'u z-(511/1000)'),
        ('u_upper',s.Rational(517,1000)-u,'(517/1000)-u z'),
        ('W_lower',W-s.Rational(181,500),'W z-(181/500)'),
        ('W_upper',s.Rational(183,500)-W,'(183/500)-W z'),
        ('b_negative',-bb,'-atomB z'),('midpoint',-mc-a/2,'-meanCosine z-atomA z/2'),
        ('mean_root_factor',-meanfactor,'-meanRootFactor z'),
        ('d_positive',d,'d z'),('gap_lower',gap-s.Rational(7,25),'meanGap z-(7/25)'),
        ('gap_square',(gap-s.Rational(7,25))**2*(G*G-1)-d*d,'(meanGap z-(7/25))^2*(G z^2-1)-d z^2'),
        ('tail_gap',s.Rational(21,20)-gap-2*u*u,'(21/20)-meanGap z-2*u z^2'),
        ('slope_positive',slope,'slope z'),('slope_lt_one',1-slope,'1-slope z'),
        ('root_minus_outer',s.Rational(-101,200)**2+a*s.Rational(-101,200)+bb,'atomPolynomial z (-101/200)'),
        ('root_minus_inner',-(s.Rational(-12,25)**2+a*s.Rational(-12,25)+bb),'-atomPolynomial z (-12/25)'),
        ('root_plus_inner',-(s.Rational(1,4)**2+a*s.Rational(1,4)+bb),'-atomPolynomial z (1/4)'),
        ('root_plus_outer',s.Rational(57,200)**2+a*s.Rational(57,200)+bb,'atomPolynomial z (57/200)'),
        ('upper_five_factor',upperfactor,'upperFiveFactor z'),
    ]
    unfold=['G','u','W','atomA','atomB','meanCosine','d','meanGap','slope','qMinus','qPlus','rMinus','rPlus','K6','F8','M10','D14','N10','eMinus','ePlus','meanRootFactor','upperFiveFactor','atomPolynomial','id_eq']
    for name,expr,actual in entries:
        print('sign proposal',name,flush=True)
        ans=b.alias(expr,name,f'(fun z : ℝ => {actual})',unfold)
        mid=ans[2].subs(z,s.Rational(6789,4000)); assert mid>0
        sg=int(s.sign(ans[3].subs(z,s.Rational(6789,4000))))
        hs='Or.inl rfl' if sg==1 else 'Or.inr rfl'
        b.lines += [f'/-- Article: exact uniform P₂ source sign {name}, with no numerical premise. -/',
                    f'theorem {name}_positive : ∀ z∈parameterInterval, 0 < ({actual}) :=',
                    f'  {name}Code.positive_check (sg := {sg}) ({hs}) (by kernel_decide) (by kernel_decide)','']
    head='''import polyak.Numerics.KernelDecide
import polyak.Certificates.P2Codes

/-! Article: Lemma p2certs. Literal exact data certify actual P₂ source signs on J. -/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
'''
    out=lean_path(root,'polyak/Certificates/P2Signs.lean')
    out.write_text(head+'\n'.join(b.lines)+'\nend\nend polyak.Boundary.P2\n')
    print(out,b.count,flush=True)


def source_builder():
    m=p2.model(False); z=m['z']; b=Builder(z); syms={}
    for key,actual in [('G','G'),('u','u'),('W','W'),('a','atomA'),('b','atomB'),('mc','meanCosine'),('d','d'),('gap','meanGap'),('slope','slope')]:
        sym=s.Symbol('SOURCE_'+key);syms[key]=sym
        n,den=s.fraction(s.cancel(m[key])); b.sub[sym]=(actual+'Code',actual,m[key],n,den)
    return m,b,syms


def real_expr(expr,syms):
    rev={v:k for k,v in syms.items()}; names={'a':'atomA','b':'atomB','mc':'meanCosine','gap':'meanGap'}
    if expr.is_Rational:return rat(expr)
    if expr in rev:return f'({names.get(rev[expr],rev[expr])} z)'
    if expr==s.Symbol('zeta'):return 'z'
    if expr.is_Add:return '('+'+'.join(real_expr(x,syms) for x in expr.args)+')'
    if expr.is_Mul:return '('+'*'.join(real_expr(x,syms) for x in expr.args)+')'
    if expr.is_Pow:
        power=int(expr.exp)
        return f'({real_expr(expr.base,syms)})^{power}' if power>=0 else f'({real_expr(expr.base,syms)})⁻¹^{(-power)}'
    raise ValueError(expr)


def generate_identities(root=None):
    m,b,syms=source_builder();z=m['z'];c=m['c']
    G,u,W,a,bb,mc=[syms[k] for k in ['G','u','W','a','b','mc']]
    M=8*G**3+4*G*G*c+4*G*c*c-4*G-W*(4*G*c*c-2*G+c)
    N=4*G*G+4*G*c-W*(4*G*c+1)
    diff=s.Poly(s.expand(-((1-c*c-u*u)*M-2*u*(1-c*c)*N)-4*G*(1-W)*(c*c+a*c+bb)**2),c)
    em,ep,N10,rm,rp,M10=[m[k] for k in ['em','ep','N10','rm','rp','M10']]
    factor=32*z**3*em*ep*(z**3+2*z-4)*N10/(rm**2*rp*M10**2)
    entries=[('mean_root_identity',mc*mc+a*mc+bb-m['f1']*factor,
              'atomPolynomial z (meanCosine z)-endpointCubic z*meanRootFactor z')]
    for k in range(5):
        e=diff.nth(k)
        if e != 0: entries.append((f'double_square_coefficient{k}',e,real_expr(e,syms)))
    unfold=['G','u','W','atomA','atomB','meanCosine','d','meanGap','slope','qMinus','qPlus','rMinus','rPlus','K6','F8','M10','D14','N10','eMinus','ePlus','meanRootFactor','atomPolynomial','endpointCubic','id_eq']
    for name,expr,actual in entries:
        ans=b.alias(expr,name,f'(fun z : ℝ => {actual})',unfold)
        assert ans[3]==0,name
        b.lines += [f'/-- Article: exact actual-source identity {name}. -/',
                    f'theorem {name} {{z : ℝ}} (hz : z∈parameterInterval) : ({actual})=0 :=',
                    f'  {name}Code.eq_zero (by kernel_decide) hz','']
    for name,expr,actual,defining in [
        ('haComposition',m['Ha'].subs(m['GG'],G),'Ha (G z)',m['N12']),
        ('switchComposition',32*G**3-36*G*G+4*G-1,'Boundary.spiralSwitch (G z)',m['f1'])]:
        ans=b.alias(expr,name,f'(fun z : ℝ => {actual})',unfold+['Ha','Boundary.spiralSwitch'])
        quo,rem=s.div(s.Poly(ans[3],z),s.Poly(defining,z));assert rem.is_zero
        denname='endpointPolynomialCode' if name=='haComposition' else 'Numerics.transitionCubicCode'
        sourceroot='N12 z=0' if name=='haComposition' else 'endpointCubic z=0'
        b.lines += [f'/-- Article: checked divisibility of the actual composed source numerator. -/',
                    f'theorem {name}_modular {{z : ℝ}} (hz : z∈parameterInterval) (hr : {sourceroot}) : ({actual})=0 := by',
                    f'  have hc : Numerics.remainderCodeCheck {name}Code.numerator {denname}.code {arr(quo.as_expr(),z)} QPoly.zero=true := by kernel_decide',
                    f'  have hd : aeval z {denname}.code.toPoly=0 := by',f'    rw [{denname}.exact]',
                    ('    rw [endpointPolynomial_eval,hr]' if name=='haComposition' else '    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using hr'),
                    '  have he := Numerics.eval_at_root_of_code hc hd',
                    f'  rw [{name}Code.exact z hz,he]',
                    '  simp [QPoly.toPoly_zero]','']
    header='''import polyak.Numerics.KernelDecide
import polyak.Certificates.P2Codes
import polyak.Boundary.P2.Roots

/-! Article: Lemmas p2ids and p2ends. Exact source-linked polynomial identities. -/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
'''
    out=lean_path(root,'polyak/Certificates/P2Identities.lean')
    out.write_text(header+'\n'.join(b.lines)+'\nend\nend polyak.Boundary.P2\n')
    print(out,b.count,flush=True)


def ring_poly(expr,var):
    p=s.Poly(s.expand(expr),var)
    if p.is_zero:return '0'
    return '('+'+'.join(f'({rat(co)})*X^{e[0]}' for e,co in p.terms())+')'


def generate_chebyshev(root=None):
    x=s.Symbol('x'); lines=['import polyak.Boundary.P2.MomentSource','',
      '/-! Article: exact finite Chebyshev expansions for the source lag certificates. -/',
      'namespace polyak.Boundary.P2','noncomputable section','open Polynomial']
    for fam,limit,fun in [('T',10,s.chebyshevt),('U',9,s.chebyshevu)]:
        for n in range(limit+1):
            rhs=ring_poly(fun(n,x),x)
            lines += [f'/-- Article: exact {fam}{n} polynomial in the finite lag prefix. -/',
                      f'theorem {fam}poly{n} : Chebyshev.{fam} ℝ {n}={rhs} := by']
            if n<2:lines += [f'  norm_num [Chebyshev.{fam}]']
            else:lines += [f'  have h := Chebyshev.{fam}_add_two ℝ ({n-2} : ℤ)',
                           f'  change Chebyshev.{fam} ℝ {n}=2*X*Chebyshev.{fam} ℝ {n-1}-Chebyshev.{fam} ℝ {n-2} at h',
                           f'  rw [{fam}poly{n-1},{fam}poly{n-2}] at h','  linear_combination h']
            lines+=['']
    lines+=['end','end polyak.Boundary.P2']
    lean_path(root,'polyak/Boundary/P2/Chebyshev.lean').write_text('\n'.join(lines)+'\n')


def generate_slacks(root=None):
    generate_chebyshev(root)
    m,b,syms=source_builder();z=m['z'];c=m['c'];GG,UU,DD=[syms[k] for k in ['G','u','d']]
    AA,BB,CC=[syms[k] for k in ['a','b','mc']]
    unfold=['G','u','W','atomA','atomB','meanCosine','d','meanGap','slope','qMinus','qPlus','rMinus','rPlus','K6','F8','M10','D14','N10','eMinus','ePlus','meanRootFactor','atomPolynomial','endpointCubic','moment','id_eq']
    for n in range(12):
        if n==0:expr=s.S.One
        elif n==1:expr=CC
        else:expr=-AA*s.Symbol(f'MOMENT_{n-1}')-BB*s.Symbol(f'MOMENT_{n-2}')
        ans=b.alias(expr,f'moment{n}',f'(fun z : ℝ => moment z {n})',[],moment_index=n)
        b.sub[s.Symbol(f'MOMENT_{n}')]=ans
    lemmas=[]
    for n in range(1,10):
        for sign in [-1,1]:
            name=('lower' if sign<0 else 'upper')+str(n)
            raw=s.Poly(s.expand((1-c*c-UU*UU)*(s.chebyshevt(n,GG)-s.chebyshevt(n,c))+sign*2*UU*(1-c*c)*s.chebyshevu(n-1,c)),c)
            expr=sum(co*s.Symbol(f'MOMENT_{e[0]}') for e,co in raw.terms())-sign*DD*s.chebyshevu(n-1,GG)
            realsyms=syms|{f'moment{k}':s.Symbol(f'MOMENT_{k}') for k in range(12)}
            # Custom real printer includes the independently specified reduced moment source.
            def pretty(e):
                for k in range(12):
                    if e==s.Symbol(f'MOMENT_{k}'):return f'(moment z {k})'
                if e.is_Add:return '('+'+'.join(pretty(a) for a in e.args)+')'
                if e.is_Mul:return '('+'*'.join(pretty(a) for a in e.args)+')'
                if e.is_Pow:return f'({pretty(e.base)})^{e.exp}'
                return real_expr(e,syms)
            actual=pretty(expr)
            rhs='('+'+'.join(f'(C ({pretty(co)}))*X^{e[0]}' for e,co in raw.terms())+')'
            sg=f'({sign} : ℝ)'
            lemmas += [f'/-- Article: exact quadratic-moment source of raw {name}. -/',
              f'theorem {name}_source (z : ℝ) : reducedSlack z {n} {sg}={actual} := by',
              '  have hpoly :',
              f'      (1-X^2-C (u z^2))*(C (Spectral.chebT {n} (G z))-Chebyshev.T ℝ {n})+',
              f'        C ({sg}*2*u z)*(1-X^2)*Chebyshev.U ℝ {n-1}={rhs} := by',
              f'    rw [Tpoly{n},Upoly{n-1}]',
              f'    norm_num [Spectral.chebT,Tpoly{n},map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]',
              '    ring','  unfold reducedSlack','  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢','  rw [hpoly]',
              '  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]',f'  norm_num [Spectral.chebU,Upoly{n-1}]',
              '  ring','']
            ans=b.alias(expr,name+'Expression',f'(fun z : ℝ => {actual})',[])
            b.lines += [f'/-- Article: compact exact representation of the actual raw {name} source. -/',
               f'def {name}ActualCode : RationalCode parameterInterval (fun z => reducedSlack z {n} {sg}) where',
               f'  numerator := {name}ExpressionCode.numerator',f'  denominator := {name}ExpressionCode.denominator',
               f'  denominator_ne := {name}ExpressionCode.denominator_ne',
               f'  exact z hz := ({name}_source z).trans ({name}ExpressionCode.exact z hz)','']
            if name in ['lower1','upper2','upper3']:
                assert ans[3]==0,name
                b.lines += [f'/-- Article: the active raw {name} is exactly zero. -/',
                            f'theorem {name}_zero {{z : ℝ}} (hz : z∈parameterInterval) : reducedSlack z {n} {sg}=0 :=',
                            f'  {name}ActualCode.eq_zero (by kernel_decide) hz','']
            elif name!='upper5':
                mid=ans[2].subs(z,s.Rational(6789,4000));assert mid>0,name
                sig=int(s.sign(ans[3].subs(z,s.Rational(6789,4000))));hs='Or.inl rfl' if sig==1 else 'Or.inr rfl'
                b.lines += [f'/-- Article: the actual raw {name} is strictly positive throughout J. -/',
                            f'theorem {name}_positive : ∀ z∈parameterInterval,0<reducedSlack z {n} {sg} :=',
                            f'  {name}ActualCode.positive_check (sg := {sig}) ({hs}) (by kernel_decide) (by kernel_decide)','']
            else:
                # The only nonzero slack with a genuine zero in J is kept as a source factorization.
                upper5=(expr,actual,ans)
    factor=(m['N10']/m['M10'])*(m['em']*m['ep']*m['qm']**3)/(8*z*z*m['rp']**2*m['rm']**7)
    expr=upper5[0]-m['N12']*factor
    actual=upper5[1]+'-N12 z*upperFiveFactor z'
    ans=b.alias(expr,'upperFiveIdentity',f'(fun z : ℝ => {actual})',['upperFiveFactor','N10','M10','eMinus','ePlus','qMinus','rMinus','rPlus','N12','id_eq'])
    assert ans[3]==0
    b.lines += [f'/-- Article: exact endpoint factor of the actual upper lag-five slack. -/',
      'theorem upper5_factor {z : ℝ} (hz : z∈parameterInterval) : reducedSlack z 5 1=N12 z*upperFiveFactor z := by',
      '  have h := upperFiveIdentityCode.eq_zero (by kernel_decide) hz',
      '  rw [upper5_source]','  linarith [h]','']
    head='''import polyak.Numerics.KernelDecide
import polyak.Boundary.P2.Chebyshev

/-! Article: exact source moment expansions for all raw lags 1 through 9. -/
namespace polyak.Boundary.P2
noncomputable section
open Polynomial
'''
    lean_path(root,'polyak/Boundary/P2/SlackSource.lean').write_text(head+'\n'.join(lemmas)+'\nend\nend polyak.Boundary.P2\n')
    header='''import polyak.Numerics.KernelDecide
import polyak.Certificates.P2Codes
import polyak.Boundary.P2.SlackSource

/-! Article: Lemma p2ids(c) and Tables p2signs/p2lags. Kernel-checked actual source slacks. -/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
'''
    out=lean_path(root,'polyak/Certificates/P2Slacks.lean')
    text='\n'.join(b.lines).replace('private def formula','def formula').replace('private def node','def node').replace('private theorem node','theorem node')
    cuts=[0]+[text.index(f'/-- Article: exact source arithmetic node {k}. -/') for k in range(81,b.count+1,80)]+[len(text)]
    previous=None
    for index,(lo,hi) in enumerate(zip(cuts,cuts[1:])):
        module=f'polyak.Certificates.P2SlacksData{index:02}'
        start=header if previous is None else f'import {previous}\n\nnamespace polyak.Boundary.P2\nnoncomputable section\nopen LeanCert.Engine Polynomial\n'
        lean_path(root,module.replace('.','/')+'.lean').write_text(start+text[lo:hi]+'\nend\nend polyak.Boundary.P2\n')
        previous=module
    out.write_text(f'import {previous}\n\n/-! Article: complete exact finite lag certificate chain for P₂. -/\n')
    print(out,b.count,len(cuts)-1,'chunks',flush=True)
    return len(cuts)-1


def generate_endpoints(root=None):
    m,b,syms=source_builder();z=m['z'];G,u,W,a,bb,mc,d=[syms[k] for k in ['G','u','W','a','b','mc','d']]
    cx=-1/(2*G);cy=(2*G-1)/(4*G)
    entries=[('lowerCandidate',cx*cx+a*cx+bb,'atomPolynomial z (-1/(2*G z))'),
             ('upperCandidate',cy*cy+a*cy+bb,'atomPolynomial z ((2*G z-1)/(4*G z))'),
             ('valueEndpoint',d-(2*G-1)*(G*G-1)/(2*G**3),'d z-(2*G z-1)*(G z^2-1)/(2*G z^3)'),
             ('weightEndpoint',W-2*(1+2*G-2*G*G)/(4*G+1),'W z-Boundary.spiralWeight (G z)'),
             ('derivativeEndpoint',syms['slope']-1/(2*G**2),'slope z-1/(2*G z^2)')]
    unfold=['atomPolynomial','Boundary.spiralWeight']
    for name,expr,actual in entries:
        ans=b.alias(expr,name,f'(fun z : ℝ => {actual})',unfold)
        quo,rem=s.div(s.Poly(ans[3],z),s.Poly(m['f1'],z));assert rem.is_zero,name
        b.lines += [f'/-- Article: exact rational endpoint identity {name} at the source cubic root. -/',
          f'theorem {name}_at_zeta1 : ({actual.replace("z", "zeta1")})=0 := by',
          f'  have hc : Numerics.remainderCodeCheck {name}Code.numerator Numerics.transitionCubicCode.code {arr(quo.as_expr(),z)} QPoly.zero=true := by kernel_decide',
          '  have hd : aeval zeta1 Numerics.transitionCubicCode.code.toPoly=0 := by',
          '    rw [Numerics.transitionCubicCode.exact]',
          '    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using endpointCubic_zeta1',
          '  have he := Numerics.eval_at_root_of_code hc hd',
          f'  have h := {name}Code.exact zeta1 zeta1_mem',
          '  rw [he] at h',
          '  simpa [QPoly.toPoly_zero] using h','']
    header='''import polyak.Numerics.KernelDecide
import polyak.Certificates.P2Codes
import polyak.Boundary.P2.Roots

/-! Article: (p2endpoint). Exact modular identities at the actual cubic endpoint. -/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
'''
    out=lean_path(root,'polyak/Certificates/P2Endpoints.lean')
    out.write_text(header+'\n'.join(b.lines)+'\nend\nend polyak.Boundary.P2\n');print(out,b.count,flush=True)


def generate_all(root=None):
    """Regenerate every exact source annotation used by the P2 Lean proof."""
    root=lean_root(root)
    generate(root)
    generate_signs(root)
    generate_identities(root)
    chunks=generate_slacks(root)
    generate_endpoints(root)
    return [
        'polyak/Certificates/P2Codes.lean',
        'polyak/Certificates/P2Signs.lean',
        'polyak/Certificates/P2Identities.lean',
        'polyak/Certificates/P2Slacks.lean',
        'polyak/Certificates/P2Endpoints.lean',
        'polyak/Boundary/P2/Chebyshev.lean',
        'polyak/Boundary/P2/SlackSource.lean',
        *[f'polyak/Certificates/P2SlacksData{i:02}.lean' for i in range(chunks)],
    ]


if __name__ == "__main__":
    generate_all()
