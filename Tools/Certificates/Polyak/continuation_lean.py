"""Compile archived central-system polynomials to source-linked Lean expressions.

The expressions and finite coefficient equalities are proposals. Lean relates
all chunks to the independently maintained regularized P5 equations before a
parametric interval checker can use them.
"""
from fractions import Fraction
from .Payload import group
from .paths import lean_root


def _rat(value):
    value = Fraction(value)
    return (str(value.numerator) if value.denominator == 1
            else f'({value.numerator}/{value.denominator})')


def _tree(operation, items, neutral):
    if not items:
        return neutral
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return f'(.{operation} {_tree(operation, items[:middle], neutral)} {_tree(operation, items[middle:], neutral)})'


def _monomial(coefficient, exponents):
    factors = [f'(.const ({_rat(coefficient)}))']
    factors.extend(f'(.var {index})' for index, power in enumerate(exponents)
                   for _ in range(power))
    return _tree('mul', factors, '(.const 1)')


def _horner(terms, variable=0):
    """Exact multivariate Horner proposal, checked against each source chunk."""
    if not terms:
        return '(.const 0)'
    if variable == len(terms[0][1]):
        return f'(.const ({_rat(sum(Fraction(c) for c,_ in terms))}))'
    groups = {}
    for coefficient, exponents in terms:
        groups.setdefault(exponents[variable], []).append((coefficient,exponents))
    powers = sorted(groups,reverse=True)
    value = _horner(groups[powers[0]],variable+1)
    previous = powers[0]
    for power in powers[1:]:
        for _ in range(previous-power):
            value = f'(.mul (.var {variable}) {value})'
        value = f'(.add {_horner(groups[power],variable+1)} {value})'
        previous = power
    for _ in range(previous):
        value = f'(.mul (.var {variable}) {value})'
    return value


def _tree_sum(items):
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return f'({_tree_sum(items[:middle])} + {_tree_sum(items[middle:])})'


def p1_source():
    polynomials = group('core')['polynomials']
    text = '''import polyak.Boundary.P1.Source
import LeanCert.Engine.RootFinding.Krawczyk
import polyak.Numerics.KernelDecide
import polyak.Numerics.Parametric.Basic

/-! Article: (p1blowup), source-linked executable P1 continuation equations. -/
namespace polyak.Certificates.Continuation.P1
open LeanCert.Core LeanCert.Engine

'''
    for i in range(2):
        record = polynomials[f'p1_F{i}']
        if record['variables'] != ['z','A','B']:
            raise ValueError('unexpected P1 continuation variable order')
        expression = _tree('add', [_monomial(a, es) for a, es in record['terms']], '(.const 0)')
        text += f'''/-- Exact executable divided P1 equation {i}. -/
def F{i} : Expr := {expression}

/-- Exact bridge to the independent P1 source, valid also at z=0. -/
theorem eval_F{i} (z : Fin 3 → ℝ) :
    evalFin F{i} z = Boundary.P1.regularEquation{i} (z 0) (z 1) (z 2) := by
  norm_num [F{i},evalFin,finEnv,Expr.eval,Boundary.P1.regularEquation{i},
    Boundary.P1.uLinear,Boundary.P1.gapLinear,Boundary.P1.atomProductLinear,
    Boundary.P1.contactQuadratic,Boundary.P1.branchU]
  ring

'''
    text += '''/-- The two divided equations with parameter first. -/
def system : Fin 2 → Expr := ![F0,F1]

'''
    text += '''/-- All expression operations admit verified automatic differentiation. -/
theorem check_supported : ∀ i, (system i).checkADSupported = true := by kernel_decide

/-- Source system equality, preserving the parameter/unknown ordering. -/
theorem source_system (z : ℝ) (x : Boundary.P1.Coordinates) :
    Numerics.Parametric.system system z x = Boundary.P1.regularSystem (z,x) := by
  ext i
  fin_cases i
'''
    for i in range(2):
        text += f'''  · change evalFin F{i} (Fin.cons z x) = _
    exact eval_F{i} (Fin.cons z x)
'''
    return text+'\nend polyak.Certificates.Continuation.P1\n'


def central_source():
    polynomials = group('p5')['polynomials']
    expected = ['h', 'A', 'B', 'y', 'P', 'D', 'w2', 'w3']
    text = '''import polyak.Boundary.P5.System
import LeanCert.Engine.RootFinding.Krawczyk
import polyak.Numerics.KernelDecide
import polyak.Numerics.Parametric.Basic

/-!
Article: (blowup), executable central equations for parameter-dependent checks.
Use: variable 0 is h; variables 1..7 are A,B,y,P,D,w2,w3.
Proof: every expression chunk equals the already source-linked polynomial chunk.
No interval outcome or external verification report is a mathematical premise.
-/
namespace polyak.Certificates.Continuation.P5
open LeanCert.Core LeanCert.Engine

'''
    for i in range(7):
        record = polynomials[f'F{i}']
        if record['variables'] != expected:
            raise ValueError('unexpected central continuation variable order')
        terms = record['terms']
        chunks = [terms[k:k+12] for k in range(0, len(terms), 12)]
        for j, chunk in enumerate(chunks):
            expression = _horner(chunk)
            text += f'''/-- Exact executable coefficient chunk {j} of equation {i}. -/
def F{i}Part{j} : Expr := {expression}

/-- The chunk has the same evaluation as the source polynomial. -/
theorem eval_F{i}Part{j} (z : Fin 8 → ℝ) :
    evalFin F{i}Part{j} z = Boundary.P5.sourceEval z Certificates.P5.F{i}Part{j} := by
  norm_num [F{i}Part{j},evalFin,finEnv,Expr.eval,Certificates.P5.F{i}Part{j},
    Boundary.P5.sourceEval]
  ring

'''
        names = [f'F{i}Part{j}' for j in range(len(chunks))]
        expression = _tree('add', names, '(.const 0)')
        evaluation = _tree_sum([f'evalFin {name} z' for name in names])
        text += f'''/-- Executable regularized central equation {i}. -/
def F{i} : Expr := {expression}

/-- Exact source bridge for equation {i}, including h=0. -/
theorem eval_F{i} (z : Fin 8 → ℝ) :
    evalFin F{i} z = Boundary.P5.sourceEval z Certificates.P5.F{i} := by
  change {evaluation} = _
  rw [{', '.join(f'eval_F{i}Part{j}' for j in range(len(chunks)))}]
  simp only [Certificates.P5.F{i},map_add]
  ring

'''
        # Whole-polynomial Horner form reduces both interval dependency and
        # repeated derivative work. Its equality is checked independently.
        expression = _horner(terms)
        unfold = ','.join(f'F{i}Part{j}' for j in range(len(chunks)))
        text += f"""/-- Compact exact Horner form of equation {i}. -/
def F{i}Horner : Expr := {expression}

theorem eval_F{i}Horner (z : Fin 8 → ℝ) : evalFin F{i}Horner z=evalFin F{i} z := by
  norm_num [F{i}Horner,F{i},{unfold},evalFin,finEnv,Expr.eval]
  ring

"""
    text += '''/-- The seven original divided equations, with parameter first. -/
def system : Fin 7 → Expr := ![F0Horner,F1Horner,F2Horner,F3Horner,F4Horner,F5Horner,F6Horner]

'''
    text += '''/-- All expression operations admit verified automatic differentiation. -/
theorem check_supported : ∀ i, (system i).checkADSupported = true := by kernel_decide

/-- Source system equality, preserving the parameter/unknown ordering. -/
theorem source_system (h : ℝ) (x : Boundary.P5.Coordinates) :
    Numerics.Parametric.system system h x = Boundary.P5.regularSystem (h,x) := by
  have he : Fin.cons h x = Boundary.P5.arguments h x := by
    ext j
    fin_cases j <;> rfl
  ext i
  fin_cases i
'''
    for i in range(7):
        text += f'''  · change evalFin F{i}Horner (Fin.cons h x) = _
    rw [eval_F{i}Horner,eval_F{i},he]
    rfl
'''
    text+='\nend polyak.Certificates.Continuation.P5\n'
    return text


def generate_all(root=None):
    root = lean_root(root)
    paths = []
    for name, content in [('P5Source', central_source()), ('P1Source', p1_source())]:
        relative = f'polyak/Certificates/Continuation/{name}.lean'
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        paths.append(relative)
    return paths
