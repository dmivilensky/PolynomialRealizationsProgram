"""Emit checks for the independently defined three-dimensional source system."""
from pathlib import Path
from .Payload import rational

OUTPUTS = frozenset({'polyak/Certificates/PartII/Exact313/System.lean'})


def q(value):
    value=rational(value)
    return f'({value.numerator}/{value.denominator})'


def generate(payload,root):
    if (not isinstance(payload,dict) or set(payload)!={'schema','center','radius','preconditioner','precision','taylor_depth'}
            or payload['schema']!='heavy-ball-exact313-system-v1'):
        raise ValueError('Unsupported exact313 source-system proposals')
    for key in ('center','radius'):
        if not isinstance(payload[key],list) or len(payload[key])!=3:
            raise ValueError('Expected three-dimensional source-system box')
    if any(rational(x)<=0 for x in payload['radius']):
        raise ValueError('Source-system radii must be positive')
    matrix=payload['preconditioner']
    if not isinstance(matrix,list) or len(matrix)!=3 or any(not isinstance(row,list) or len(row)!=3 for row in matrix):
        raise ValueError('Expected 3x3 source-system preconditioner')
    precision,depth=payload['precision'],payload['taylor_depth']
    if type(precision)is not int or not -512<=precision<=-48 or type(depth)is not int or not 20<=depth<=100:
        raise ValueError('Invalid source-system evaluation parameters')
    center=','.join(map(q,payload['center']));radius=','.join(map(q,payload['radius']))
    inverse=';'.join(','.join(map(q,row)) for row in matrix)
    target=Path(root)/next(iter(OUTPUTS));target.parent.mkdir(parents=True,exist_ok=True)
    text=f'''import polyak.CertifiedExamples.Exact313.SystemCode
import polyak.CertifiedExamples.Trigonometry
import polyak.CertifiedExamples.Exact313.GeometryCode
import polyak.Certificates.PartII.Exact313.Root

namespace polyak.Certificates.PartII.Exact313.System
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric
open polyak.CertifiedExamples.Exact313

def certificate : WeightedCertificate 3 where
  center := ![{center}]
  radius := ![{radius}]
  preconditioner := !![{inverse}]

def config : DyadicConfig := {{precision:={precision},taylorDepth:={depth}}}

theorem accepted : checkDyadic SystemCode.equations
    polyak.CertifiedExamples.Trigonometry.piTight certificate config=true := by
  kernel_decide

theorem nonsingular : SystemCode.nonsingularCheck
    polyak.CertifiedExamples.Trigonometry.piTight
    (coordinateBox certificate.center certificate.radius)
    certificate.preconditioner config=true := by
  kernel_decide

'''
    for i,name in enumerate(('constant','linear','quadratic')):
        box=f'(coordinateBox certificate.center certificate.radius {i})'
        for side,expression in [('lower',f'.sub Code.{name} (.const {box}.lo)'),
                                ('upper',f'.sub (.const {box}.hi) Code.{name}')]:
            text+=f'''theorem coefficient_{side}_{i} : boundCheck ({expression})
    polyak.Certificates.PartII.Exact313.piBox
    (coordinateBox polyak.Certificates.PartII.Exact313.certificate.center
      polyak.Certificates.PartII.Exact313.certificate.radius)
    polyak.Certificates.PartII.Exact313.config true=true := by
  kernel_decide

'''
    text+='end polyak.Certificates.PartII.Exact313.System\n'
    target.write_text(text)
    return sorted(OUTPUTS)
