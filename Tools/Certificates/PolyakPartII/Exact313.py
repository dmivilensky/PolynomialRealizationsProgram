"""Compile exact-3/13 rational proposals to ordinary kernel-checked Lean."""
from fractions import Fraction
from pathlib import Path

OUTPUTS = frozenset({'polyak/Certificates/PartII/Exact313/Root.lean', 'polyak/Certificates/PartII/Exact313/Reserves.lean', 'polyak/Certificates/PartII/Exact313/Location.lean'})


def _rat(data):
    if (not isinstance(data, list) or len(data) != 2
            or any(type(x) is not int for x in data) or data[1] <= 0):
        raise ValueError('expected canonical rational [numerator,positive denominator]')
    q = Fraction(*data)
    if [q.numerator, q.denominator] != data:
        raise ValueError('noncanonical rational')
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'


def generate(payload, staging_root):
    if set(payload) != {'format', 'version', 'scalar_root', 'stable_root', 'normalized_u', 'evaluation'}:
        raise ValueError('unexpected exact313 payload keys')
    if payload['format'] != 'HEAVY_BALL_EXACT313_DATA' or payload['version'] != 1:
        raise ValueError('unsupported exact313 proposal format')
    root = payload['scalar_root']
    if set(root) != {'center', 'radius', 'preconditioner'}:
        raise ValueError('unexpected scalar_root fields')
    center, radius, preconditioner = (_rat(root[key]) for key in
                                     ('center', 'radius', 'preconditioner'))
    cfg = payload['evaluation']
    if set(cfg) != {'precision', 'taylor_depth'}:
        raise ValueError('unexpected evaluation fields')
    precision, depth = cfg['precision'], cfg['taylor_depth']
    if type(precision) is not int or not -512 <= precision <= -48:
        raise ValueError('invalid precision')
    if type(depth) is not int or not 10 <= depth <= 80:
        raise ValueError('invalid Taylor depth')
    stable = payload['stable_root']
    if set(stable) != {'lower', 'upper'}:
        raise ValueError('unexpected stable_root fields')
    lower, upper = _rat(stable['lower']), _rat(stable['upper'])
    normalized_u = payload['normalized_u']
    if set(normalized_u) != {'lower', 'upper'}:
        raise ValueError('unexpected normalized_u fields')
    ulo, uhi = _rat(normalized_u['lower']), _rat(normalized_u['upper'])
    target = Path(staging_root) / 'polyak/Certificates/PartII/Exact313/Root.lean'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(f'''import polyak.CertifiedExamples.Exact313.Code
import polyak.Numerics.KernelDecide
import Mathlib.Analysis.Real.Pi.Bounds

/-! Generated rational proposals for the exact 3/13 source equation. -/
namespace polyak.Certificates.PartII.Exact313
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric

def piBox : IntervalRat :=
  ⟨314159265358979323846/100000000000000000000,
    314159265358979323847/100000000000000000000,by norm_num⟩

def certificate : WeightedCertificate 1 where
  center := ![{center}]
  radius := ![{radius}]
  preconditioner := !![{preconditioner}]

def config : DyadicConfig := {{precision:={precision},taylorDepth:={depth}}}

theorem accepted : checkDyadic
    polyak.CertifiedExamples.Exact313.Code.equations piBox certificate config=true := by
  kernel_decide

end polyak.Certificates.PartII.Exact313
''', encoding='utf-8')
    target = Path(staging_root) / 'polyak/Certificates/PartII/Exact313/Reserves.lean'
    target.write_text("""import polyak.CertifiedExamples.Exact313.GeometryCode
import polyak.Certificates.PartII.Exact313.Root

/-! Every concrete reserve is independently recomputed by the kernel. -/
namespace polyak.Certificates.PartII.Exact313
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric

""" + ''.join(f"theorem reserve{i:02d} : boundCheck\n    (polyak.CertifiedExamples.Exact313.Code.reserves {i})\n    piBox (coordinateBox certificate.center certificate.radius) config true=true := by\n  kernel_decide\n\n" for i in range(17)) +
    "end polyak.Certificates.PartII.Exact313\n", encoding='utf-8')
    target = Path(staging_root) / 'polyak/Certificates/PartII/Exact313/Location.lean'
    target.write_text(f"""import polyak.CertifiedExamples.Exact313.LocationCode
import polyak.Certificates.PartII.Exact313.Root

/-! Kernel-recomputed secular endpoint signs and original-parameter location. -/
namespace polyak.Certificates.PartII.Exact313
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric
open polyak.CertifiedExamples.Exact313

def stableBox : IntervalRat := ⟨{lower},{upper},by norm_num⟩
def uBox : IntervalRat := ⟨{ulo},{uhi},by norm_num⟩
def secularReserves : Fin 5→Expr := ![
  .neg (Code.secularAt (.const {lower})),
  Code.secularAt (.const {upper}),
  .add (.const {lower}) (.mul (.const 2) Code.quadratic),
  .sub (.const {lower}) Code.linear,
  .add (.const {lower}) Code.linear]

""" + ''.join(f"theorem secular{i:02d} : boundCheck\n    (secularReserves {i}) piBox\n    (coordinateBox certificate.center certificate.radius) config true=true := by\n  kernel_decide\n\n" for i in range(5)) +
    f"def intermediateBox : Fin 2→IntervalRat := ![coordinateBox certificate.center certificate.radius 0,stableBox]\n\ndef squareReserves : Fin 2→Expr := ![\n  .sub (.mul (.var 2) Code.normalizedB) (.const ({ulo}^2)),\n  .sub (.const ({uhi}^2)) (.mul (.var 2) Code.normalizedB)]\n\ndef locationBox : Fin 3→IntervalRat := ![coordinateBox certificate.center certificate.radius 0,stableBox,uBox]\n\n" +
    ''.join(f"theorem square{i:02d} : boundCheck\n    (squareReserves {i}) piBox intermediateBox config true=true := by\n  kernel_decide\n\n" for i in range(2)) +
    ''.join(f"theorem location{i:02d} : boundCheck\n    (Code.locationReserves {i}) piBox locationBox config true=true := by\n  kernel_decide\n\n" for i in range(6)) +
    "end polyak.Certificates.PartII.Exact313\n", encoding='utf-8')
    return list(OUTPUTS)
