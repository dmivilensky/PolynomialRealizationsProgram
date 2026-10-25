"""Materialize already-proved P2 rational arrays for executable endpoint graphs."""
from fractions import Fraction
from .Payload import group
from .paths import lean_path


def output_names():
    return ['polyak/Certificates/Continuation/P5EndpointGraphs.lean']


def _array(record):
    if record['variables'] != ['zeta']:
        raise ValueError('unexpected P5 endpoint rational variable order')
    values={es[0]:Fraction(q) for q,es in record['terms']}
    coeffs=[values.get(i,Fraction(0)) for i in range(max(values,default=0)+1)]
    def rat(q):return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
    return '⟨#['+','.join(rat(q) for q in coeffs)+']⟩'


def generate(root=None):
    rationals=group('p2')['rationals']
    text='''import polyak.Certificates.P2Codes
import polyak.Numerics.RationalExpr

/-! Article: (p5arc), executable algebraic endpoint source graphs.
Each literal pair is definitionally equal to the previously proved P2 source
representation. No rational identity or root location is assumed here. -/
namespace polyak.Certificates.Continuation.P5EndpointGraphs
open LeanCert.Core LeanCert.Engine Numerics

'''
    for key,name in [('G','G'),('u','u'),('a','atomA'),('b','atomB'),('mc','meanCosine'),('d','d'),('W','W')]:
        r=rationals[key]
        text+=f'''def {name} : Expr := .mul
  (polynomialExpr ({_array(r['numerator'])} : QPoly) (.var 0))
  (.inv (polynomialExpr ({_array(r['denominator'])} : QPoly) (.var 0)))

theorem {name}_exact : {name}=Boundary.P2.{name}Code.expression := rfl

'''
    text+='end polyak.Certificates.Continuation.P5EndpointGraphs\n'
    lean_path(root,output_names()[0]).write_text(text,encoding='utf-8')
    return output_names()
