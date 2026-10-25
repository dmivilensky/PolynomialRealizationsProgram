"""Translate the two selected exact mathematical plateau proposals.

The archive contributes intervals and covering subdivisions.  Formulae are
fixed by the local consumer and the independent Lean source definitions.
"""
from fractions import Fraction as F
from pathlib import Path

from .Payload import rational

OUTPUTS = frozenset({'polyak/Certificates/PartII/Plateaus/Data.lean',
                     'polyak/Certificates/PartII/Plateaus/Numerical.lean',
                     'polyak/Certificates/PartII/Plateaus/PrimaryNumerical.lean'})


def _q(v):
    q=rational(v)
    return f'({q.numerator}/{q.denominator})'


def _I(v):
    if not isinstance(v,list) or len(v)!=2 or rational(v[0])>rational(v[1]):
        raise ValueError('invalid plateau interval')
    return f'⟨{_q(v[0])},{_q(v[1])},by norm_num⟩'


def generate(payload,stagingRoot):
    if (not isinstance(payload,dict) or set(payload)!={'schema','rows'} or
            payload['schema']!='heavy-ball-selected-plateaus-v1' or
            not isinstance(payload['rows'],list)):
        raise ValueError('invalid selected plateau proposals')
    expected={'2/9':(18,[3,4],F(2201327,1000000),F(1567,2500),[[1,19],[-4,14]]),
              '5/21':(21,[3,4,5],F(89631,40000),F(769,1250),[[1,-20],[-12,9],[-4,-25]])}
    rows={}
    required={'name','gap','y','beta','period','numerators','pairs','kappa_bracket',
              'cosine_boxes','near_radius','symbol_cells','right_kernel_boxes',
              'xi_boxes',
              'matrix_boxes','slope_matrix_boxes','slope_target_boxes','slope_moment_boxes',
              'pinning_matrix_boxes','pinning_determinant_box',
              'left_kernel_boxes','determinant_endpoint_boxes','rank_minor_box',
              'slope_determinant_box','inactive_residue_boxes','minimizer_box',
              'dual_weight_boxes'}
    for row in payload['rows']:
        if not isinstance(row,dict) or set(row)!=required or row['name'] not in expected:
            raise ValueError('invalid plateau row')
        name=row['name'];L,S,y,beta,pairs=expected[name]
        if name in rows or (row['gap'],row['period'],row['numerators'],
                rational(row['y']),rational(row['beta']),row['pairs'])!=(4,L,S,y,beta,pairs):
            raise ValueError('selected plateau source mismatch')
        d=len(S)
        for field in ['cosine_boxes','right_kernel_boxes','left_kernel_boxes']:
            if len(row[field])!=d:raise ValueError('wrong plateau dimension')
            for interval in row[field]:_I(interval)
        if len(row['xi_boxes'])!=3:raise ValueError('Xi dimension')
        for interval in row['xi_boxes']:_I(interval)
        for field in ['matrix_boxes','slope_matrix_boxes','pinning_matrix_boxes']:
            if len(row[field])!=d or any(len(r)!=d for r in row[field]):
                raise ValueError('matrix dimensions')
            for r in row[field]:
                for interval in r:_I(interval)
        for field in ['slope_target_boxes','slope_moment_boxes']:
            if len(row[field])!=d:raise ValueError('slope dimensions')
            for interval in row[field]:_I(interval)
        if len(row['determinant_endpoint_boxes'])!=2:raise ValueError('root endpoints')
        for interval in row['determinant_endpoint_boxes']:_I(interval)
        for field in ['kappa_bracket','rank_minor_box','slope_determinant_box','pinning_determinant_box','minimizer_box']:
            _I(row[field])
        if set(row['dual_weight_boxes'])!={str(n) for pair in pairs for n in pair}:
            raise ValueError('unexpected dual lags')
        if set(row['inactive_residue_boxes'])!={str(r) for r in range(1,L)
                if r not in {p[0]%L for p in pairs}}:
            raise ValueError('inactive residue coverage')
        for field in ['dual_weight_boxes','inactive_residue_boxes']:
            for interval in row[field].values():_I(interval)
        rational(row['near_radius'])
        if not row['symbol_cells']:raise ValueError('empty symbol cover')
        for cell in row['symbol_cells']:
            if set(cell)!={'lo','hi','kind'} or cell['kind'] not in ('value','curvature'):
                raise ValueError('invalid symbol cell')
            _I([cell['lo'],cell['hi']])
        rows[name]=row
    if set(rows)!=set(expected):raise ValueError('missing selected plateau row')
    lines=['import polyak.CertifiedExamples.Plateaus.Arithmetic',
           'import polyak.Numerics.KernelDecide','',
           '/-! Rational proposals from the independent Heavy-Ball proof archive. -/',
           'namespace polyak.Certificates.PartII.Plateaus',
           'open LeanCert.Core','']
    for name,row in rows.items():
        L,S,_,_,_=expected[name];d=len(S);tag=f'row{L}'
        lines += [f'def {tag}Y : ℚ := {_q(row["y"])}',
                  f'def {tag}Beta : ℚ := {_q(row["beta"])}',
                  f'def {tag}Kappa : IntervalRat := {_I(row["kappa_bracket"])}',
                  f'def {tag}Cosines : Fin {d} → IntervalRat := !['+
                  ','.join(_I(v) for v in row['cosine_boxes'])+']',
                  f'def {tag}Xi : Fin 3 → IntervalRat := !['+
                  ','.join(_I(v) for v in row['xi_boxes'])+']',
                  f'def {tag}Matrix : Fin {d} → Fin {d} → IntervalRat := !['+
                  ','.join('!['+','.join(_I(v) for v in r)+']' for r in row['matrix_boxes'])+']',
                  f'def {tag}Slope : Fin {d} → Fin {d} → IntervalRat := !['+
                  ','.join('!['+','.join(_I(v) for v in r)+']' for r in row['slope_matrix_boxes'])+']',
                  f'def {tag}Pinning : Fin {d} → Fin {d} → IntervalRat := !['+
                  ','.join('!['+','.join(_I(v) for v in r)+']' for r in row['pinning_matrix_boxes'])+']',
                  f'def {tag}Target : Fin {d} → IntervalRat := !['+
                  ','.join(_I(v) for v in row['slope_target_boxes'])+']',
                  f'def {tag}Moments : Fin {d} → IntervalRat := !['+
                  ','.join(_I(v) for v in row['slope_moment_boxes'])+']',
                  f'def {tag}SlopeDet : IntervalRat := {_I(row["slope_determinant_box"])}',
                  f'def {tag}PinningDet : IntervalRat := {_I(row["pinning_determinant_box"])}',
                  f'def {tag}RankMinor : IntervalRat := {_I(row["rank_minor_box"])}',
                  f'def {tag}Lags : Fin {2*d} → ℤ := !['+
                  ','.join(str(n) for pair in row['pairs'] for n in pair)+']',
                  f'def {tag}DualBoxes : Fin {2*d} → IntervalRat := !['+
                  ','.join(_I(row['dual_weight_boxes'][str(n)]) for pair in row['pairs'] for n in pair)+']',
                  f'def {tag}Right : Fin {d} → IntervalRat := !['+
                  ','.join(_I(v) for v in row['right_kernel_boxes'])+']',
                  f'def {tag}Left : Fin {d} → IntervalRat := !['+
                  ','.join(_I(v) for v in row['left_kernel_boxes'])+']',
                  f'def {tag}Dual : List (ℤ × IntervalRat) := ['+
                  ','.join(f'({n},{_I(v)})' for n,v in sorted(row['dual_weight_boxes'].items(),key=lambda a:int(a[0])))+']',
                  f'def {tag}SymbolCells : List (IntervalRat × Bool) := ['+
                  ','.join(f'({_I([c["lo"],c["hi"]])},{str(c["kind"]=="curvature").lower()})'
                           for c in row['symbol_cells'])+']','']
    lines += ['end polyak.Certificates.PartII.Plateaus','']
    text='\n'.join(lines)
    numerical='''import polyak.Certificates.PartII.Plateaus.Data
import polyak.CertifiedExamples.Plateaus.Root
import polyak.CertifiedExamples.Trigonometry

/-! These rejecting finite checks validate the proposed strict interval signs;
the source semantics and regularity assembly use the handwritten modules. -/
namespace polyak.Certificates.PartII.Plateaus
open LeanCert.Core
open polyak.CertifiedExamples.Plateaus chebyshev2.Numerics

'''
    for name,row in rows.items():
        L,S,_,_,_=expected[name];d=len(S);tag=f'row{L}'
        numerical += f'''theorem {tag}_right_positive :
    ∀ i, 0<({tag}Right i).lo := by kernel_decide

theorem {tag}_left_positive :
    ∀ i, 0<({tag}Left i).lo := by kernel_decide

theorem {tag}_dual_positive :
    ∀ p ∈ {tag}Dual, 0<p.2.lo := by kernel_decide

'''
        cs='!['+','.join(f'Real.cos (2*Real.pi*{j}/{L})' for j in S)+']'
        numerical+=f'''theorem {tag}_cosines_mem :
    ∀ i, ({cs} : Fin {d} → ℝ) i ∈ {tag}Cosines i := by
  intro i
  fin_cases i
'''
        for j,box in zip(S,row['cosine_boxes']):
            lo,hi=map(_q,box)
            numerical+=f'''  · have h := CertifiedExamples.Trigonometry.cos_bounds (2*{j}/{L}) 32 {lo} {hi}
      (by kernel_decide)
    have he : (((2*{j}/{L}):ℚ):ℝ)*Real.pi = 2*Real.pi*{j}/{L} := by push_cast; ring
    rw [he] at h
    exact h
'''
        signs=[]
        for endpoint,number in enumerate(row['kappa_bracket']):
            kval=_q(number)
            neg=rational(row['determinant_endpoint_boxes'][endpoint][1])<0
            signs.append(neg)
            expr=f'determinant{L}Expr {kval}'
            if not neg:expr=f'IntervalExpr.neg ({expr})'
            relation=f'determinant{L} {kval}<0' if neg else f'0<determinant{L} {kval}'
            numerical+=f'''theorem {tag}_endpoint{endpoint}_sign : {relation} := by
  have h := IntervalExpr.strictNegative_sound ({expr}) {tag}Cosines
    (by kernel_decide) {tag}_cosines_mem
'''
            if neg:
                numerical+=f'  rw [determinant{L}Expr_value] at h\n  push_cast at h\n  exact h\n\n'
            else:
                numerical+=f'''  change -(determinant{L}Expr {kval}).value {cs} < 0 at h
  rw [determinant{L}Expr_value] at h
  push_cast at h
  exact neg_lt_zero.mp h

'''
        klo,khi=map(_q,row['kappa_bracket'])
        conj=(f'⟨{tag}_endpoint0_sign,{tag}_endpoint1_sign⟩' if signs[0] else
              f'⟨{tag}_endpoint1_sign,{tag}_endpoint0_sign⟩')
        alt='Or.inl' if signs[0] else 'Or.inr'
        numerical+=f'''theorem {tag}_boundary_root :
    ∃ κ ∈ Set.Icc ({klo}:ℝ) {khi}, determinant{L} κ=0 :=
  polynomial_root_from_opposite_signs continuous_determinant{L} (by norm_num)
    ({alt} {conj})

'''
    numerical+='end polyak.Certificates.PartII.Plateaus\n'
    primary='''import polyak.Certificates.PartII.Plateaus.Data
import polyak.CertifiedExamples.Plateaus.CoordinateCode
import polyak.CertifiedExamples.Plateaus.KernelExpressions
import polyak.CertifiedExamples.Plateaus.Enclosure
import polyak.CertifiedExamples.Plateaus.Blocks
import polyak.CertifiedExamples.Plateaus.PinningCode

/-! Finite rejecting checks for the actual polynomial matrix, adjugate
kernels, derivative system and positive lifted dual weights. -/
namespace polyak.Certificates.PartII.Plateaus
open polyak.CertifiedExamples.Plateaus LeanCert.Core chebyshev2.Numerics

'''
    for name,row in rows.items():
        L,S,_,_,pairs=expected[name];d=len(S);tag=f'row{L}';N=3+d
        reps='!['+','.join(str(p[0]) for p in pairs)+']'
        lifts='!['+','.join(str(p[1]) for p in pairs)+']'
        coordbox='!['+','.join(f'{tag}Xi {i}' for i in range(3))+','+','.join(f'{tag}Cosines {i}' for i in range(d))+']'
        primary+=f'''def {tag}CoordinateBox : Fin {N} → IntervalRat := {coordbox}

def {tag}LagExpr (n:ℤ) (order:ℕ) (i:Fin {d}) : E {N} :=
  coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] n order
    (.variable (Fin.natAdd 3 i))

theorem {tag}_matrix_checked : ∀ r i,
    enclosed ({tag}LagExpr (({reps}:Fin {d}→ℤ) r) 0 i)
      {tag}CoordinateBox ({tag}Matrix r i)=true := by kernel_decide

theorem {tag}_slope_checked : ∀ r i,
    enclosed (minus ({tag}LagExpr (({lifts}:Fin {d}→ℤ) r) 1 i)
      ({tag}LagExpr (({reps}:Fin {d}→ℤ) r) 1 i))
      {tag}CoordinateBox ({tag}Slope i r)=true := by kernel_decide

theorem {tag}_pinning_checked : ∀ r i,
    enclosed (pinningExpr {L} ![.variable 0,.variable 1,.variable 2]
      (({reps}:Fin {d}→ℤ) r) (.variable (Fin.natAdd 3 i)))
      {tag}CoordinateBox ({tag}Pinning i r)=true := by kernel_decide

def {tag}MatrixBox : Fin {d*d} → IntervalRat := fun z =>
  {tag}Matrix ((finProdFinEquiv (m:={d}) (n:={d})).symm z).1 ((finProdFinEquiv (m:={d}) (n:={d})).symm z).2

def {tag}MatrixVariables : Fin {d} → Fin {d} → E {d*d} := fun i j =>
  matrixVariables {d} i j

theorem {tag}_left_checked : ∀ i,
    enclosed (left{d}Expr {tag}MatrixVariables i) {tag}MatrixBox ({tag}Left i)=true := by
  kernel_decide

theorem {tag}_right_checked : ∀ i,
    enclosed (right{d}Expr {tag}MatrixVariables i) {tag}MatrixBox ({tag}Right i)=true := by
  kernel_decide

def {tag}SlopeBox : Fin {d*d} → IntervalRat := fun z =>
  {tag}Slope ((finProdFinEquiv (m:={d}) (n:={d})).symm z).1 ((finProdFinEquiv (m:={d}) (n:={d})).symm z).2

theorem {tag}_slope_det_checked :
    enclosed (det{d}Expr {tag}MatrixVariables) {tag}SlopeBox {tag}SlopeDet=true := by
  kernel_decide

def {tag}PinningBox : Fin {d*d} → IntervalRat := fun z =>
  {tag}Pinning ((finProdFinEquiv (m:={d}) (n:={d})).symm z).1 ((finProdFinEquiv (m:={d}) (n:={d})).symm z).2

theorem {tag}_pinning_det_checked :
    enclosed (det{d}Expr {tag}MatrixVariables) {tag}PinningBox {tag}PinningDet=true := by
  kernel_decide

'''
        minor=(f'{tag}MatrixVariables 1 1' if d==2 else
               f'det2Expr (fun i j=>{tag}MatrixVariables (Fin.succ i) (Fin.succ j))')
        primary+=f'''theorem {tag}_rank_minor_checked :
    enclosed ({minor}) {tag}MatrixBox {tag}RankMinor=true := by kernel_decide

'''
        # Keep target and moment stages separate. This prevents repeated
        # interval evaluation of the same adjugate graph in every slope test.
        tbox='!['+','.join(f'{tag}Xi {i}' for i in range(3))+','+','.join(f'{tag}Cosines {i}' for i in range(d))+','+','.join(f'{tag}Left {i}' for i in range(d))+']'
        primary+=f'def {tag}TargetBox : Fin {3+2*d} → IntervalRat := {tbox}\n\n'
        def local_lag(n,order,i,dim):
            return f'coordinateCodeExpr (d:={dim}) ![.variable 0,.variable 1,.variable 2] ({n}) {order} (.variable {3+i})'
        for i in range(d):
            terms=[f'times (.variable {3+d+j}) ({local_lag(pairs[j][0],1,i,3+2*d)})' for j in range(d)]
            expr=terms[0]
            for t in terms[1:]:expr=f'plus ({expr}) ({t})'
            primary+=f'''theorem {tag}_target{i}_checked :
    enclosed (.neg ({expr})) {tag}TargetBox ({tag}Target {i})=true := by kernel_decide

'''
        generic_terms=[f'times (.variable {3+d+j}) (coordinateCodeExpr ![.variable 0,.variable 1,.variable 2] ({pairs[j][0]}) 1 (.variable ⟨3+i.val,by omega⟩))' for j in range(d)]
        generic_expr=generic_terms[0]
        for t in generic_terms[1:]:generic_expr=f'plus ({generic_expr}) ({t})'
        primary+=f'''def {tag}TargetExpr (i:Fin {d}) : E {3+2*d} :=
  .neg ({generic_expr})

theorem {tag}_target_checked : ∀ i,
    enclosed ({tag}TargetExpr i) {tag}TargetBox ({tag}Target i)=true := by kernel_decide

'''
        mbox=f'Fin.append {tag}SlopeBox {tag}Target'
        primary+=f'''def {tag}MomentBox : Fin {d*d+d} → IntervalRat := {mbox}

def {tag}MomentMatrix : Fin {d} → Fin {d} → E {d*d+d} := fun i j =>
  matrixBlock (a:={d}) i j

def {tag}MomentTarget : Fin {d} → E {d*d+d} := fun i =>
  blockSecond (a:={d*d}) i

theorem {tag}_moments_checked : ∀ i,
    enclosed (moments{d}Expr {tag}MomentMatrix {tag}MomentTarget i)
      {tag}MomentBox ({tag}Moments i)=true := by kernel_decide

'''
        lambox='!['+','.join(f'{tag}Left {i}' for i in range(d))+','+','.join(f'{tag}Moments {i}' for i in range(d))+']'
        primary+=f'def {tag}LiftBox : Fin {2*d} → IntervalRat := {lambox}\n\n'
        for j in range(2*d):
            expr=f'minus (.variable {j//2}) (.variable {d+j//2})' if j%2==0 else f'IntervalExpr.variable {d+j//2}'
            primary+=f'''theorem {tag}_lift{j}_checked :
    enclosed ({expr}) {tag}LiftBox ({tag}DualBoxes {j})=true := by kernel_decide

'''
    primary+='end polyak.Certificates.PartII.Plateaus\n'
    texts={ 'polyak/Certificates/PartII/Plateaus/Data.lean':text,
            'polyak/Certificates/PartII/Plateaus/Numerical.lean':numerical,
            'polyak/Certificates/PartII/Plateaus/PrimaryNumerical.lean':primary}
    for relative,body in texts.items():
        path=Path(stagingRoot)/relative
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(body,encoding='utf-8')
    return sorted(OUTPUTS)
