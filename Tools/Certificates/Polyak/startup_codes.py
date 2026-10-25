"""Propose source-linked Lean rational identities for initialized-spiral data.

Every source is the named mathematical expression in ExplicitSpiral/Source.
The emitted Lean program composes proved rational operations, checks exact
coefficient cross products, and proves denominator signs on rho,q>0.
"""
from dataclasses import dataclass
from pathlib import Path
from .paths import lean_root
from functools import reduce
import sympy as s

from .startup import RHO as r, Q as q, _coefficients, integer_source, source


@dataclass
class Entry:
    key: str
    target: str
    recipe: object
    actual: object
    proof: str


def recipes(limit=None):
    entries=[]; actual={}; target={}; symbols={}
    def add(key,goal,expr,proof):
        expr=s.sympify(expr)
        expanded=s.cancel(expr.xreplace(actual))
        symbol=s.Symbol(key)
        entries.append(Entry(key,goal,expr,expanded,proof))
        actual[symbol]=expanded;target[symbol]=goal;symbols[key]=symbol
        return symbol
    def basic(key,name,expr):
        return add(key,f"Source.{name} z.1"+(" z.2" if name in {
            'multiplierReal','multiplierImag','defectReal','defectImag','defectNorm','valueConstant'} else ''),
                   expr,f"simp only [Source.{name}]\n    norm_num <;> ring")
    G=basic('hG','hyperbolic',(r+1/r)/2)
    g=basic('hGap','gap',2*r*(r*r-r+1)/(r*r+1)**2)
    real=basic('hReal','lambdaReal',-r*r/(r*r+1))
    imsq=basic('hImSq','imaginarySquare',r*r-real**2)
    c=add('hCos','radialCosine',-r/(r*r+1),'') if False else None
    c=add('hCos','radialCosine z.1',-r/(r*r+1),
          'simp only [radialCosine]\n    norm_num <;> ring')
    sr=basic('hSReal','multiplierReal',-(r*r+q*q)/(2*q*(r*r+1)))
    si=basic('hSImag','multiplierImag',(r*r-q*q)/(2*q*r*r))
    dr=basic('hDReal','defectReal',q*(r*r+2)/(2*(r*r+1)))
    di=basic('hDImag','defectImag',q/(2*r*r))
    dn=basic('hDNorm','defectNorm',dr**2+imsq*di**2)
    reserve=add('hReserve','Source.reserve z.2',(1-q**4)**2,
                'simp only [Source.reserve]\n    norm_num <;> ring')
    epsilon=add('hEpsilon','phaseBudget z.1',s.Rational(3,40)*(r*r-1)*(r+1)**2/(r*(r*r+1)),
                'simp only [phaseBudget]\n    norm_num <;> ring')
    b=basic('hValue','valueConstant',(g*(r*r-1)/(r*r+1)+2*sr)/4)
    if limit is not None and limit<=13:
        return entries[:limit],target
    Ts=[];Us=[]
    for family,rows in [('T',Ts),('U',Us)]:
        for k in range(10):
            expr=1 if k==0 else (c if family=='T' else 2*c) if k==1 else 2*c*rows[-1]-rows[-2]
            goal=f'polyak.Spectral.cheb{family} {k} (radialCosine z.1)'
            proof=(f'norm_num [polyak.Spectral.cheb{family}]' if k<2 else
                   f'rw [Source.cheb{family}_rec {k-2}]\n    ring')
            rows.append(add(f'h{family}{k}',goal,expr,proof))
    coeff={}
    for sign,label in [(-1,'Lower'),(1,'Upper')]:
        ar=add('hAlphaReal'+label,f'Source.alphaReal z.1 z.2 ({sign})',
               (dr*(sr-sign)+imsq*di*si)/2,'simp only [Source.alphaReal]\n    norm_num <;> ring')
        ai=add('hAlphaImag'+label,f'Source.alphaImag z.1 z.2 ({sign})',
               (dr*si-di*(sr-sign))/2,'simp only [Source.alphaImag]\n    norm_num <;> ring')
        br=add('hBetaReal'+label,f'Source.betaReal z.1 z.2 ({sign})',
               g*G*real/r+ar,'simp only [Source.betaReal]\n    norm_num <;> ring')
        bi=add('hBetaImag'+label,f'Source.betaImag z.1 z.2 ({sign})',
               sign*g*G/r+ai,'simp only [Source.betaImag]\n    norm_num <;> ring')
        bn=add('hBetaNorm'+label,f'Source.betaNorm z.1 z.2 ({sign})',br**2+imsq*bi**2,
               'simp only [Source.betaNorm]\n    norm_num <;> ring')
        a=add('hQuadratic'+label,f'Source.quadratic z.1 ({sign})',
              g/(4*G)*((1-sign)/(2*r)+s.Rational(1+sign,2)*r),
              'simp only [Source.quadratic]\n    norm_num <;> ring')
        gamma=add('hConstant'+label,f'Source.constant z.1 z.2 ({sign})',
                  g/(4*G)*(s.Rational(1-sign,2)*r+(1+sign)/(2*r))-ar-dn/4,
                  'simp only [Source.constant]\n    norm_num <;> ring')
        residues=[]
        for j in range(3):
            e=br if j==0 else br*Ts[j]-imsq/r*bi*Us[j-1]
            residues.append(add(f'hResidue{label}{j}',f'Source.residue z.1 z.2 ({sign}) {j}',e,
                       'simp only [Source.residue]\n    norm_num <;> ring'))
        coeff[sign]=(a,gamma,bn,residues)
    pairs={}
    for k in range(1,10):
        pr=add(f'hPowerReal{k}',f'Source.powerReal z.1 {k}',r**k*Ts[k],
               'simp only [Source.powerReal]\n    norm_num <;> ring')
        pi=add(f'hPowerImag{k}',f'Source.powerImag z.1 {k}',r**(k-1)*Us[k-1],
               'simp only [Source.powerImag]\n    norm_num <;> ring')
        gr=add(f'hGradientReal{k}',f'Source.gradientReal z.1 z.2 {k}',sr*pr-imsq*si*pi,
               'simp only [Source.gradientReal]\n    norm_num <;> ring')
        gi=add(f'hGradientImag{k}',f'Source.gradientImag z.1 z.2 {k}',sr*pi+si*pr,
               'simp only [Source.gradientImag]\n    norm_num <;> ring')
        rad=add(f'hRadius{k}',f'Source.radius z.1 z.2 {k}',
                ((pr-1)**2+imsq*pi**2-(gr-(sr+dr))**2-imsq*(gi-(si+di))**2)/4,
                'simp only [Source.radius]\n    norm_num <;> ring')
        disc=add(f'hDiscrepancy{k}',f'Source.discrepancy z.1 z.2 {k}',
                b*(r**(2*k)-1)-((sr+dr+gr)*(pr-1)+imsq*(si+di+gi)*pi)/2,
                'simp only [Source.discrepancy]\n    norm_num <;> ring')
        for sign,label in [(-1,'Lower'),(1,'Upper')]:
            pairs[sign,k]=add(f'hPair{label}{k}',f'Source.pairSlack z.1 z.2 ({sign}) {k}',
                rad+sign*disc+(1-(-q*q)**((k+1)//2))**2,
                'simp only [Source.pairSlack]\n    norm_num <;> ring')
    for index,(name,expected,lo,hi) in enumerate(source()):
        bits=name.split('.')
        sign=-1 if 'lower' in bits else 1
        a,gamma,bn,res=coeff[sign]
        if bits[0]=='I':
            expr=gamma+reserve if bits[-1]=='constant' else (gamma+reserve)**2-bn
        elif bits[0]=='II':
            if bits[-1]=='beta': expr=1-bn
            elif bits[-1]=='quadratic': expr=a-epsilon
            else:
                A=a-epsilon;B=res[int(bits[2])]+epsilon;C=gamma+reserve
                expr=A+B+C if bits[-1]=='at_one' else 2*A+B if bits[-1]=='derivative' else 4*A*C-B*B
        elif bits[1].startswith('k'):
            expr=pairs[sign,int(bits[1][1:])]
        else:
            Z=a*r**20+gamma+reserve
            expr=4*a*a*r**20-bn if bits[-1]=='derivative' else Z if bits[-1]=='constant' else Z*Z-bn*r**20
        closed=s.cancel(expr.xreplace(actual))
        if s.cancel(closed-expected)!=0:
            raise ValueError('source mismatch: '+name)
        key=f'check{index:02d}'
        # The final source is a mathematical combination of already specified named expressions.
        goal=real_term(expr,target)
        add(key,goal,expr,'ring')
    return entries,target


def rat(n):
    n=s.Rational(n)
    return (str(n.p) if n.p>=0 else f'({n.p})') if n.q==1 else f'({n.p}/{n.q})'


def real_term(expr,targets):
    if expr==r:return 'z.1'
    if expr==q:return 'z.2'
    if expr in targets:return '('+targets[expr]+')'
    if expr.is_Rational:return '(('+rat(expr)+' : ℚ) : ℝ)'
    if expr.is_Add:return '('+'+'.join(real_term(a,targets) for a in expr.args)+')'
    if expr.is_Mul:return '('+'*'.join(real_term(a,targets) for a in expr.args)+')'
    if expr.is_Pow:
        base='('+real_term(expr.base,targets)+')'
        n=int(expr.exp)
        if n<0:
            return base+'⁻¹' if n==-1 else '('+base+'⁻¹)'+f'^{ -n}'
        return base+f'^{n}'
    raise ValueError(expr)


def code_term(expr,targets):
    if expr==r:return '(RationalCode.first Source.domain)'
    if expr==q:return '(RationalCode.second Source.domain)'
    if expr in targets:return str(expr)+'Code'
    if expr.is_Rational:return '(RationalCode.constant Source.domain '+rat(expr)+')'
    if expr.is_Add:return reduce(lambda a,b:f'({a}.add {b})',(code_term(a,targets) for a in expr.args))
    if expr.is_Mul:return reduce(lambda a,b:f'({a}.mul {b})',(code_term(a,targets) for a in expr.args))
    if expr.is_Pow:
        base=code_term(expr.base,targets)
        n=int(expr.exp)
        if n>=0:return f'({base}.pow {n})'
        goal=real_term(expr.base,targets)
        inverse=f'''({base}.invOfSource (by
      intro z hz
      have hr : 0<z.1 := hz.1
      have hq : 0<z.2 := hz.2
      {"dsimp only [Source.hyperbolic]" if s.Symbol('hG') in expr.base.free_symbols else ""}
      positivity))'''
        return inverse if n==-1 else f'({inverse}.pow {-n})'
    raise ValueError(expr)


def int_source(poly):
    return integer_source(poly)


def list_literal(rows):
    return '['+','.join('['+','.join(str(c) for c in row)+']' for row in rows)+']'


def proof_script(entry):
    if entry.proof=='ring':
        return 'rfl'
    if entry.proof.startswith('simp only ['):
        name=entry.proof.split('[',1)[1].split(']',1)[0]
        ds=f'dsimp only [{name}]'
        if entry.key in {'hDNorm','hBetaNormLower','hBetaNormUpper','hResidueLower0','hResidueUpper0'}:
            return 'rfl'
        if entry.key.startswith('hPowerImag'):
            return 'rw [Source.powerImag,ite_eq_right (by decide)]; ring'
        if entry.key.startswith('hResidue'):
            return f'rw [Source.residue,ite_eq_right (by decide)]; ring'
        if entry.key in {'hGap','hSReal','hEpsilon','hValue'}:
            return ds+'; field_simp; ring'
        return ds+'; ring'

    return entry.proof.replace('\n    ring','; ring')


def emit_signs(path):
    entries,_=recipes()
    checks=[e for e in entries if e.key.startswith('check')]
    text=['import polyak.Certificates.Startup.Codes']
    text += [f'import polyak.Certificates.Startup.Check{i:02d}' for i in range(44)]
    text += ['\n/-! Article: the 44 exact signs for the actual initialized-spiral source. -/',
             'namespace polyak.Certificates.Startup.Signs',
             'noncomputable section',
             'open polyak.Realization.ExplicitSpiral',
             'open polyak.Numerics.BivariateBranch',
             'open polyak.Certificates.Startup']
    for i,e in enumerate(checks):
        target=e.target.replace('z.1','r').replace('z.2','q')
        text.append(f'''/-- Article: kernel-certified source sign {i:02d}, with its physical branch. -/
theorem sign{i:02d} {{r q : ℝ}} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check{i:02d}.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<{target} := by
  rw [Codes.{e.key}Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check{i:02d}.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.{e.key}Denominator (by kernel_decide) hr hq
''')
    text+=['end','end polyak.Certificates.Startup.Signs']
    Path(path).write_text('\n'.join(text)+'\n')
    return len(checks)


@dataclass(frozen=True)
class ASTNode:
    """One source expression with a canonical checked rational representation."""
    expression: object
    actual: object
    goal: str
    code: str


class ASTBuilder:
    """Recode every binary arithmetic node before composing the next operation.

    The cache is global across source entries and emitted modules.  A cached
    node always retains its ordinary real source expression; the proposed
    coefficient arrays occur only in the RationalCode proof layer.
    """
    def __init__(self, targets):
        self.targets = targets
        self.cache = {}
        self.pending = []
        self.nodes = []
        self.counter = 0

    def register(self, entry):
        symbol = s.Symbol(entry.key)
        self.cache[symbol] = ASTNode(symbol, entry.actual, '('+entry.target+')', entry.key+'Code')

    def _leaf(self, expr):
        if expr == r:
            return ASTNode(expr, expr, 'z.1', '(RationalCode.first Source.domain)')
        if expr == q:
            return ASTNode(expr, expr, 'z.2', '(RationalCode.second Source.domain)')
        if expr.is_Rational:
            return ASTNode(expr, expr, real_term(expr,self.targets),
                           '(RationalCode.constant Source.domain '+rat(expr)+')')
        raise ValueError('unregistered source symbol: '+str(expr))

    def _emit(self, expr, actual, goal, raw):
        if expr in self.cache:
            return self.cache[expr]
        key = f'hAst{self.counter:03d}'
        self.counter += 1
        actual = s.cancel(actual)
        n,d = s.fraction(actual)
        if any(c<0 for row in int_source(d) for c in row):
            raise ValueError('AST denominator coefficient sign: '+key)
        block = f'''/-- Article: canonical numerator for one arithmetic source node. -/
def {key}Numerator : polyak.Numerics.IntegerBivariate.Source := {list_literal(int_source(n))}
/-- Article: canonical positive denominator for the same real source node. -/
def {key}Denominator : polyak.Numerics.IntegerBivariate.Source := {list_literal(int_source(d))}
/-- Article: one source-preserving arithmetic operation on already reduced operands. -/
def {key}Raw : RationalCode Source.domain (fun {"z" if "z." in goal else "_"} => {goal}) :=
  {raw}
private theorem {key}DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients {key}Denominator=true := by kernel_decide
private theorem {key}DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode {key}Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    {key}Denominator {key}DenCheck hz.1 hz.2).ne'
/-- Article: checked exact cancellation of this single arithmetic operation. -/
theorem {key}Cross : equalCheck
    (mul {key}Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode {key}Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode {key}Numerator) {key}Raw.denominator)=true := by
  kernel_decide
/-- Article: the original real source node with its canonical exact rational code. -/
def {key}Code : RationalCode Source.domain (fun {"z" if "z." in goal else "_"} => {goal}) :=
  {key}Raw.recode
    (polyak.Numerics.IntegerBivariate.rationalCode {key}Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode {key}Denominator)
    {key}DenNonzero {key}Cross
'''
        self.pending.append(block)
        node = ASTNode(expr,actual,goal,key+'Code')
        self.cache[expr] = node
        self.nodes.append(node)
        return node

    def _binary(self, operation, left, right):
        if operation == 'add':
            expr,actual = left.expression+right.expression,left.actual+right.actual
            operator = '+'
        elif operation == 'mul':
            expr,actual = left.expression*right.expression,left.actual*right.actual
            operator = '*'
        else:
            raise ValueError(operation)
        # A source cache hit may choose a different associative presentation;
        # callers retain that node's real goal, and only the outer source-name
        # identity needs the elementary ring reassociation.
        return self._emit(expr,actual,'('+left.goal+operator+right.goal+')',
                          f'({left.code}.{operation} {right.code})')

    def _inverse(self, base):
        raw = f'''({base.code}.invOfSource (by
    intro z hz
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    {"dsimp only [Source.hyperbolic]" if s.Symbol('hG') in base.expression.free_symbols else ""}
    positivity))'''
        return self._emit(base.expression**-1,1/base.actual,'('+base.goal+')⁻¹',raw)

    def _power(self, base, degree):
        return self._emit(base.expression**degree,base.actual**degree,
                          '('+base.goal+')^'+str(degree),f'({base.code}.pow {degree})')

    def build(self, expr):
        expr = s.sympify(expr)
        if expr in self.cache:
            return self.cache[expr]
        if expr in (r,q) or expr.is_Rational:
            node = self._leaf(expr)
            self.cache[expr] = node
            return node
        if expr.is_Add or expr.is_Mul:
            nodes = [self.build(a) for a in expr.args]
            op = 'add' if expr.is_Add else 'mul'
            result = nodes[0]
            for node in nodes[1:]:
                result = self._binary(op,result,node)
            return result
        if expr.is_Pow and expr.exp.is_Integer:
            base = self.build(expr.base)
            degree = int(expr.exp)
            if degree < 0:
                base = self._inverse(base)
                degree = -degree
            return base if degree == 1 else self._power(base,degree)
        raise ValueError('unsupported arithmetic source AST: '+str(expr))

    def take_pending(self):
        blocks,self.pending = self.pending,[]
        return blocks


def emit_split(directory, chunk_size=10):
    """Emit topological modules, reducing each later arithmetic AST node."""
    entries,targets=recipes()
    directory=Path(directory)
    headers=['import polyak.Numerics.KernelDecide','import polyak.Numerics.BivariateAlgebra',
             'import polyak.Numerics.PositiveCoefficients',
             'import polyak.Realization.ExplicitSpiral.Source']
    modules=[]
    builder=ASTBuilder(targets)
    for start in range(0,len(entries),chunk_size):
        name=f'Code{len(modules):02d}'
        lines=headers[:] if not modules else [f'import polyak.Certificates.Startup.{modules[-1]}']
        lines+=['\n/-! Article: exact source identities for initialized special-spiral data. -/',
                'namespace polyak.Certificates.Startup.Codes','noncomputable section',
                'open polyak.Numerics.BivariateBranch',
                'open polyak.Realization.ExplicitSpiral']
        for index,e in enumerate(entries[start:start+chunk_size],start):
            n,d=s.fraction(e.actual)
            if any(c<0 for row in int_source(d) for c in row):
                raise ValueError('denominator coefficient sign: '+e.key)
            if index < 53:
                raw=code_term(e.recipe,targets)
            else:
                node=builder.build(e.recipe)
                if s.cancel(node.actual-e.actual)!=0:
                    raise ValueError('AST source mismatch: '+e.key)
                lines.extend(builder.take_pending())
                raw=f'''({node.code}.congr (by
    intro z hz
    ring))'''
            lines.append(f'''/-- Article: proposed exact numerator for {e.key}. -/
def {e.key}Numerator : polyak.Numerics.IntegerBivariate.Source := {list_literal(int_source(n))}
/-- Article: proposed positive denominator for {e.key}. -/
def {e.key}Denominator : polyak.Numerics.IntegerBivariate.Source := {list_literal(int_source(d))}
/-- Article: composition of proved source-preserving rational operations. -/
def {e.key}Raw : RationalCode Source.domain (fun {"z" if e.recipe.free_symbols else "_"} => {real_term(e.recipe,targets)}) :=
  {raw}
private theorem {e.key}Identity (z : ℝ×ℝ) (hz : z∈Source.domain) :
    {real_term(e.recipe,targets)}={e.target} := by
    have hr : 0<z.1 := hz.1
    have hq : 0<z.2 := hz.2
    have hG : Source.hyperbolic z.1≠0 := by unfold Source.hyperbolic; positivity
    {proof_script(e)}
private theorem {e.key}DenCheck :
    polyak.Numerics.IntegerBivariate.positiveCoefficients {e.key}Denominator=true := by kernel_decide
private theorem {e.key}DenNonzero (z : ℝ×ℝ) (hz : z∈Source.domain) :
    value (polyak.Numerics.IntegerBivariate.rationalCode {e.key}Denominator) z.1 z.2≠0 :=
  (polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
    {e.key}Denominator {e.key}DenCheck hz.1 hz.2).ne'
private theorem {e.key}Cross : equalCheck
    (mul {e.key}Raw.numerator (polyak.Numerics.IntegerBivariate.rationalCode {e.key}Denominator))
    (mul (polyak.Numerics.IntegerBivariate.rationalCode {e.key}Numerator) {e.key}Raw.denominator)=true := by
  kernel_decide
/-- Article: source-linked exact rational representation for {e.key}. -/
def {e.key}Code : RationalCode Source.domain (fun z => {e.target}) :=
  ({e.key}Raw.congr {e.key}Identity).recode
    (polyak.Numerics.IntegerBivariate.rationalCode {e.key}Numerator)
    (polyak.Numerics.IntegerBivariate.rationalCode {e.key}Denominator)
    {e.key}DenNonzero {e.key}Cross
''')
            builder.register(e)
        lines+=['end','end polyak.Certificates.Startup.Codes']
        (directory/f'{name}.lean').write_text('\n'.join(lines)+'\n')
        modules.append(name)
    (directory/'Codes.lean').write_text(
        f'import polyak.Certificates.Startup.{modules[-1]}\n\n'
        '/-! Article: all exact source identities for the initialized special spiral. -/\n')
    return len(entries),modules


def generate_all(root=None):
    """Regenerate all exact initialized-spiral proposals for kernel checking."""
    from .startup import lean_numerator_modules
    root=lean_root(root)
    directory=root/'polyak/Certificates/Startup'
    directory.mkdir(parents=True,exist_ok=True)
    paths=lean_numerator_modules(directory)
    _,modules=emit_split(directory)
    emit_signs(directory/'Signs.lean')
    return [*[str(Path(path).relative_to(root)) for path in paths],
            *[str((directory/(name+'.lean')).relative_to(root)) for name in modules],
            str((directory/'Codes.lean').relative_to(root)),
            str((directory/'Signs.lean').relative_to(root))]


if __name__=='__main__':
    generate_all()
