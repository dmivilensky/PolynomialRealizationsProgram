"""Propose derivative boxes for the source-linked central continuation.

The rational derivative centres are obtained by exact linear algebra at the
archived slab centres, then rounded to a fixed rational grid.  Their residuals,
norm defects, and physical signs are independently checked by Lean's kernel.
No numerical derivative or external success flag is a theorem premise.
"""
from fractions import Fraction
import sympy as sp
from .Payload import group, polynomial
from .continuation_boxes import CENTRAL_LAYOUT, coarsen
from .continuation_lean import _rat
from .paths import lean_path
from .derivative_proposals import central_derivative_boxes


def output_names():
    return [f'polyak/Certificates/Continuation/P5Slope/Batch{i:03d}.lean'
            for i in range(len(CENTRAL_LAYOUT))] + [
                'polyak/Certificates/Continuation/P5Slope.lean']


def derivative_centers(records):
    variables = sp.symbols('h A B y P D w2 w3')
    source = group('p5')['polynomials']
    equations = [sp.Poly(polynomial(source[f'F{i}']), *variables, domain=sp.QQ)
                 for i in range(7)]
    derivatives = [[equation.diff(variable) for variable in variables]
                   for equation in equations]
    result = []
    scale = 10**9
    for record in records:
        midpoint = sum(map(Fraction, record['parameter'])) / 2
        values = [sp.Rational(midpoint)] + list(map(sp.Rational, record['centre']))
        substitution = dict(zip(variables, values))
        jacobian = sp.Matrix([[entry.eval(substitution) for entry in row]
                              for row in derivatives])
        solution = jacobian[:, 1:].inv(method='DM') * (-jacobian[:, 0])
        rounded = []
        for value in solution:
            numerator, denominator = map(int, sp.fraction(value))
            nearest = (2*numerator*scale + denominator) // (2*denominator)
            rounded.append(Fraction(nearest, scale))
        result.append(rounded)
    return result


def generate(root=None):
    records = coarsen('central', CENTRAL_LAYOUT)
    centers = derivative_centers(records)
    files = {}
    for i, center in enumerate(centers):
        label = f'Batch{i:03d}'
        radius = '![213/250,321/25,21/5,144/5,6,87/250,21/125]'
        jacobian, parameter = central_derivative_boxes(records[i])
        def interval(bounds):
            return f'⟨{_rat(bounds[0])},{_rat(bounds[1])},by norm_num⟩'
        text = f'''import polyak.Boundary.P5.SlopeCheck
import polyak.Certificates.Continuation.P5Batches.{label}
import polyak.Numerics.KernelDecide

/-! Article: central-family actual source derivative reserves, slab {i}. -/
namespace polyak.Certificates.Continuation.P5.Slope.{label}
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 7 → ℚ := ![''' + ','.join(_rat(c) for c in center) + f''']
def radius : Fin 7 → ℚ := {radius}

'''
        text += 'def jacobianBox : Matrix (Fin 7) (Fin 7) IntervalRat := !['
        text += ','.join('!['+','.join(map(interval,row))+']' for row in jacobian)+']\n\n'
        text += 'def parameterBox : Fin 7 → IntervalRat := !['
        text += ','.join(map(interval,parameter))+']\n\n'
        for row in range(7):
            text += f'''theorem row{row} :
    (∀ j : Fin 7,derivativeEntryCheck (P5.system {row})
      (LeanCert.Engine.finBoxEnv (box P5.{label}.I0
        (coordinateBox P5.{label}.C0.center P5.{label}.C0.radius)))
      j.succ.val {{precision:=-80}} (jacobianBox {row} j)=true) ∧
    derivativeEntryCheck (P5.system {row})
      (LeanCert.Engine.finBoxEnv (box P5.{label}.I0
        (coordinateBox P5.{label}.C0.center P5.{label}.C0.radius)))
      0 {{precision:=-80}} (parameterBox {row})=true := by kernel_decide

'''
        text += f'''theorem derivatives : derivativeEnclosureCheck P5.system P5.{label}.I0
    (coordinateBox P5.{label}.C0.center P5.{label}.C0.radius)
    jacobianBox parameterBox {{precision:=-80}}=true := by
  simp only [derivativeEnclosureCheck,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro i j
    fin_cases i
'''
        for row in range(7):
            text += f'    · exact row{row}.1 j\n'
        text += '  · intro i\n    fin_cases i\n'
        for row in range(7):
            text += f'    · exact row{row}.2\n'
        text += f'''
theorem accepted : sourceSlopeCheck P5.{label}.I0 P5.{label}.C0
    center radius jacobianBox parameterBox=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Slope.{label}
'''
        files[f'polyak/Certificates/Continuation/P5Slope/{label}.lean'] = text
    text = ''.join(f'import polyak.Certificates.Continuation.P5Slope.Batch{i:03d}\n'
                   for i in range(len(records)))
    text += '''import polyak.Certificates.Continuation.P5Family

/-! Article: complete checked derivative reserves on the actual source cover. -/
namespace polyak.Certificates.Continuation.P5.Slope
open LeanCert.Core Numerics.Parametric Boundary.P5

'''
    for name in ('center', 'radius'):
        text += f'def {name} : Fin {len(records)} → (Fin 7 → ℚ) := !['
        text += ','.join(f'Batch{i:03d}.{name}' for i in range(len(records))) + ']\n\n'
    text += f'''theorem checked (i : Fin {len(records)}) :
    ∃ (J : Matrix (Fin 7) (Fin 7) IntervalRat) (p : Fin 7 → IntervalRat),
      derivativeEnclosureCheck P5.system (P5.table i).domain
        (coordinateBox (P5.table i).certificate.center (P5.table i).certificate.radius)
        J p {{precision:=-80}}=true ∧
      sourceSlopeCheck (P5.table i).domain (P5.table i).certificate
        (center i) (radius i) J p=true := by
  fin_cases i
'''
    for i in range(len(records)):
        text += f'  · exact ⟨Batch{i:03d}.jacobianBox,Batch{i:03d}.parameterBox,Batch{i:03d}.derivatives,Batch{i:03d}.accepted⟩\n'
    text += '\nend polyak.Certificates.Continuation.P5.Slope\n'
    files['polyak/Certificates/Continuation/P5Slope.lean'] = text
    for path, content in files.items():
        lean_path(root, path).write_text(content, encoding='utf-8')
    return list(files)
