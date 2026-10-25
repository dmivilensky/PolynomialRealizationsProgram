"""Kernel proposals for every finite P5 prefix on archived continuation boxes."""
from .paths import lean_path


def output_names():
    return ([f'polyak/Certificates/Continuation/P5Prefix/Batch{i:03d}.lean' for i in range(20)] +
            ['polyak/Certificates/Continuation/P5Properties.lean'])


def _file(batch):
    ns=f'P5.Batch{batch:03d}'
    text=f'''import polyak.Boundary.P5.PrefixCheck
import polyak.Boundary.P5.GeometryCheck
import polyak.Certificates.Continuation.P5LagCodes
import polyak.Certificates.Continuation.P5Batches.Batch{batch:03d}
import polyak.Numerics.KernelDecide

/-! Article: (p5arc), source-linked finite inactive lag certificates on slab {batch}.
All active slacks follow from the original source equations; every other lag
is checked after exact cancellation of the critical parameter factor. -/
namespace polyak.Certificates.Continuation.P5Prefix.Batch{batch:03d}
open Boundary.P5 Numerics.Parametric

'''
    for n in range(1,24):
        for b,label in ((False,'Lower'),(True,'Upper')):
            if (n,b) in ((1,False),(2,True),(3,True),(5,True)):
                continue
            text+=f'''private theorem lag{n:02d}{label} : lagCheck {n} P5Lags.lag{n:02d} {str(b).lower()}
    {ns}.I0 (coordinateBox {ns}.C0.center {ns}.C0.radius) {{precision:=-80}}=true := by
  kernel_decide

'''
    text+=f'''theorem accepted : prefixCheck P5Lags.codes {ns}.I0 {ns}.C0 {{precision:=-80}}=true := by
  simp only [prefixCheck,decide_eq_true_eq]
  intro n b hn
  fin_cases n
'''
    text+='  · norm_num at hn\n'
    for n in range(1,24):
        text+='  · cases b\n'
        for b,label in ((False,'Lower'),(True,'Upper')):
            proof='by kernel_decide' if (n,b) in ((1,False),(2,True),(3,True),(5,True)) else f'lag{n:02d}{label}'
            text+=f'    · exact {proof}\n'
    text+=f'''
theorem geometryAccepted : continuationGeometryCheck {ns}.I0 {ns}.C0 {{precision:=-80}}=true := by
  kernel_decide
'''
    return text+f'\nend polyak.Certificates.Continuation.P5Prefix.Batch{batch:03d}\n'


def _properties():
    text='import polyak.Boundary.P5.SlabProperties\nimport polyak.Certificates.Continuation.P5Cover\n'
    text+=''.join(f'import polyak.Certificates.Continuation.P5Prefix.Batch{i:03d}\n' for i in range(20))
    text+='\n/-! Article: (p5arc), all finite source properties on the complete continuation cover. -/\n'
    text+='namespace polyak.Certificates.Continuation.P5Properties\nopen Boundary.P5 Numerics.Parametric\n\n'
    for family in ['Prefix','Geometry']:
        pred='allPrefixCheck P5Lags.codes' if family=='Prefix' else 'allGeometryCheck'
        pname='prefix' if family=='Prefix' else 'geometry'
        for i in range(20):
            theorem='accepted' if family=='Prefix' else 'geometryAccepted'
            text+=f'private theorem {pname}{i:03d} : {pred} P5.Batch{i:03d}.slabs {{precision:=-80}}=true := by\n'
            text+=f'  simpa only [{"allPrefixCheck" if family=="Prefix" else "allGeometryCheck"},P5.Batch{i:03d}.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch{i:03d}.{theorem}\n\n'
        proof=f'{pname}019'
        for i in reversed(range(19)):
            call='allPrefixCheck_append P5Lags.codes' if family=='Prefix' else 'allGeometryCheck_append'
            proof=f'({call} {pname}{i:03d} {proof})'
        text+=f'theorem {pname}Accepted : {pred} P5.slabs {{precision:=-80}}=true :=\n  {proof}\n\n'
    return text+'end polyak.Certificates.Continuation.P5Properties\n'


def generate(root=None):
    names=output_names()
    for batch,name in enumerate(names[:20]):
        path=lean_path(root,name)
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(_file(batch),encoding='utf-8')
    lean_path(root,names[20]).write_text(_properties(),encoding='utf-8')
    return names
