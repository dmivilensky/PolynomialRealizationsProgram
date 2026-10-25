"""Propose coarsened exact continuation boxes, never accepting a numerical claim.

Ranges and inflation are local certificate-layout choices. Each resulting slab
must separately pass the formal checker. No external cover/success flag is used.
"""
from fractions import Fraction
from .Payload import interval_proposals
from .continuation_lean import _rat
from .paths import lean_path


def coarsen(family, spans, inflation=Fraction(3)):
    source = interval_proposals(family)
    expected = {'p1': ('z', ['A','B']),
                'central': ('h', ['A','B','y','P','D','w2','w3'])}
    parameter, unknowns = expected[family]
    if source.get('parameter') != parameter or source.get('unknown_order') != unknowns:
        raise ValueError('unexpected continuation parameter or unknown order')
    boxes = source['boxes']
    n = len(unknowns)
    for box in boxes:
        if (len(box['centre']) != n or len(box['radii']) != n or
                len(box['inverse']) != n or any(len(row) != n for row in box['inverse'])):
            raise ValueError('unexpected continuation box dimension')
    result = []
    for lo, hi in spans:
        if not 0 <= lo < hi <= len(boxes):
            raise ValueError('continuation span outside the archived box table')
        chunk = boxes[lo:hi]
        middle = chunk[len(chunk)//2]
        center = list(map(Fraction, middle['centre']))
        radius = [inflation*max(abs(Fraction(record['centre'][j])-value) +
                               Fraction(record['radii'][j]) for record in chunk)
                  for j, value in enumerate(center)]
        # The producer's central row 0 is four times the independent Lean
        # regularized row 0.  R*diag(4,1,...,1) is only a proposed inverse;
        # the source-linked formal checker proves its contraction itself.
        inverse = [[str(Fraction(value)*(4 if family == 'central' and j == 0 else 1))
                    for j,value in enumerate(row)] for row in middle['inverse']]
        result.append(dict(parameter=[chunk[0]['parameter'][0],chunk[-1]['parameter'][1]],
                           centre=list(map(str,center)),radii=list(map(str,radius)),
                           inverse=inverse,origin=[lo,hi]))
    return result


def definitions(records, dimension):
    text = ''
    for index, record in enumerate(records):
        text += f'def I{index} : IntervalRat := ⟨{_rat(record["parameter"][0])},{_rat(record["parameter"][1])},by norm_num⟩\n'
        text += f'def C{index} : WeightedCertificate {dimension} := '+'{center:=!['
        text += ','.join(_rat(c) for c in record['centre'])+'],radius:=!['
        text += ','.join(_rat(c) for c in record['radii'])+'],preconditioner:=!['
        text += ','.join('!['+','.join(_rat(c) for c in row)+']' for row in record['inverse'])+']}\n'
    return text


def diagnostic(records, family):
    """Native diagnostic only; retained candidates still need kernel acceptance."""
    label, dimension = ('P1', 2) if family == 'p1' else ('P5', 7)
    checker = 'checkDyadic' if family == 'p1' else 'checkCorrelated'
    text = f'''import polyak.Numerics.Parametric.Slab
import polyak.Numerics.Parametric.Correlated
import polyak.Certificates.Continuation.{label}Source
open LeanCert.Core polyak.Numerics.Parametric
namespace Candidate
'''+definitions(records,dimension)
    text += f'def proposals : Array (Slab {dimension}) := #['+','.join(
        f'⟨I{i},C{i}⟩' for i in range(len(records)))+']\n'
    return text+f'''#eval proposals.toList.zipIdx.forM (fun (entry : Slab {dimension} × ℕ) => do
  let slab := entry.1
  let result := {checker} polyak.Certificates.Continuation.{label}.system
    slab.domain slab.certificate {{precision:=-80}}
  IO.println s!"{{entry.2}}: {{result}}"
  (← IO.getStdout).flush)
end Candidate
'''


# Reviewed partition only; all interval values still come from the pinned archive.
P1_LAYOUT = ((0, 40), (40, 80), (80, 120), (120, 160), (160, 200), (200, 240), (240, 280), (280, 320), (320, 360), (360, 400), (400, 440), (440, 480), (480, 520), (520, 560), (560, 600), (600, 640), (640, 680), (680, 720), (720, 760), (760, 800), (800, 840), (840, 880), (880, 920), (920, 960), (960, 1000), (1000, 1040), (1040, 1080), (1080, 1120), (1120, 1160), (1160, 1200), (1200, 1240), (1240, 1280), (1280, 1320), (1320, 1360), (1360, 1400), (1400, 1440), (1440, 1480), (1480, 1520), (1520, 1560), (1560, 1600), (1600, 1640), (1640, 1680), (1680, 1720), (1720, 1760), (1760, 1800), (1800, 1840), (1840, 1880), (1880, 1920), (1920, 1960), (1960, 2000), (2000, 2040), (2040, 2080), (2080, 2120), (2120, 2160), (2160, 2200), (2200, 2240), (2240, 2280), (2280, 2320), (2320, 2360), (2360, 2400), (2400, 2440), (2440, 2480), (2480, 2520), (2520, 2560), (2560, 2600), (2600, 2640), (2640, 2680), (2680, 2720), (2720, 2760), (2760, 2800), (2800, 2840), (2840, 2880), (2880, 2920), (2920, 2960), (2960, 3000), (3000, 3040), (3040, 3080), (3080, 3120), (3120, 3160), (3160, 3200), (3200, 3240), (3240, 3280), (3280, 3320), (3320, 3360), (3360, 3400), (3400, 3440), (3440, 3480), (3480, 3520), (3520, 3540), (3540, 3560), (3560, 3580), (3580, 3600), (3600, 3620), (3620, 3640), (3640, 3660), (3660, 3680), (3680, 3690), (3690, 3700), (3700, 3710), (3710, 3720), (3720, 3730), (3730, 3740), (3740, 3750), (3750, 3760), (3760, 3770), (3770, 3780), (3780, 3790), (3790, 3800), (3800, 3805), (3805, 3810), (3810, 3815), (3815, 3820), (3820, 3825), (3825, 3830), (3830, 3835), (3835, 3840), (3840, 3845), (3845, 3850), (3850, 3855), (3855, 3860), (3860, 3865), (3865, 3870), (3870, 3875), (3875, 3880), (3880, 3885), (3885, 3890), (3890, 3895), (3895, 3900), (3900, 3905), (3905, 3910), (3910, 3915), (3915, 3920), (3920, 3925), (3925, 3930), (3930, 3935), (3935, 3940), (3940, 3945), (3945, 3950), (3950, 3955), (3955, 3960), (3960, 3965), (3965, 3967), (3967, 3970), (3970, 3972), (3972, 3975), (3975, 3977), (3977, 3980), (3980, 3982), (3982, 3985), (3985, 3987), (3987, 3990), (3990, 3992), (3992, 3995), (3995, 3997), (3997, 4000))


def p1_batches(records):
    chunks = [records[i:i+10] for i in range(0,len(records),10)]
    result = {}
    for index, chunk in enumerate(chunks):
        name = f'Batch{index:03d}'
        text = f"""import polyak.Numerics.Parametric.Slab
import polyak.Certificates.Continuation.P1Source

/-! Article: Appendix B P1 continuation, exact accepted slab batch {index}. -/
namespace polyak.Certificates.Continuation.P1.{name}
open LeanCert.Core Numerics.Parametric

"""+definitions(chunk,2)
        text += '\ndef slabs : List (Slab 2) := ['+','.join(
            f'⟨I{i},C{i}⟩' for i in range(len(chunk)))+']\n'
        text += """
/-- Every real parameter in every listed slab has an actual unique source root. -/
theorem accepted : allAccepted P1.system slabs {precision:=-80}=true := by
  kernel_decide

"""+f'end polyak.Certificates.Continuation.P1.{name}\n'
        result[f'polyak/Certificates/Continuation/P1Batches/{name}.lean'] = text
    names = [f'Batch{i:03d}' for i in range(len(chunks))]
    text = ''.join(f'import polyak.Certificates.Continuation.P1Batches.{name}\n'
                   for name in names)
    text += """
/-! Article: Appendix B P1 continuation, complete closed-interval root coverage. -/
namespace polyak.Certificates.Continuation.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

"""
    expression = names[-1]+'.slabs'
    proof = names[-1]+'.accepted'
    for name in reversed(names[:-1]):
        expression = f'({name}.slabs ++ {expression})'
        proof = f'(allAccepted_append {name}.accepted {proof})'
    text += f'def slabs : List (Slab 2) := {expression}\n\n'
    text += f'theorem accepted : allAccepted system slabs {{precision:=-80}}=true :=\n  {proof}\n\n'
    text += """/-- Actual rational endpoints cover the entire claimed closed parameter domain. -/
theorem covered : coverCheck 0 (733/1000) slabs=true := by kernel_decide

/-- Existence and box-local uniqueness for the actual, independently defined P1 system. -/
theorem source_roots {z : ℝ} (hz : z∈Set.Icc (0 : ℝ) (733/1000)) :
    ∃ slab∈slabs, z∈slab.domain ∧ ∃! x,
      FinBoxMem x (coordinateBox slab.certificate.center slab.certificate.radius) ∧
        Boundary.P1.regularSystem (z,x)=0 := by
  obtain ⟨slab,hmem,hz,hroot⟩ := cover_roots system slabs {precision:=-80}
    0 (733/1000) covered accepted (s:=z) (by norm_num at *; exact hz)
  exact ⟨slab,hmem,hz,by simpa only [source_system] using hroot⟩

end polyak.Certificates.Continuation.P1
"""
    result['polyak/Certificates/Continuation/P1Cover.lean'] = text
    return result


# The central family uses correlated parameter residuals and one slab per
# kernel proof, keeping each exact decision within the ordinary resource limits.
CENTRAL_LAYOUT = tuple((i,i+200) for i in range(0,4000,200))

def central_batches(records):
    chunks = [records[i:i+1] for i in range(0,len(records),1)]
    result = {}
    for index, chunk in enumerate(chunks):
        name = f'Batch{index:03d}'
        text = f"""import polyak.Numerics.Parametric.CorrelatedSlab
import polyak.Certificates.Continuation.P5Source

/-! Article: Appendix B P5 continuation, exact accepted slab batch {index}. -/
namespace polyak.Certificates.Continuation.P5.{name}
open LeanCert.Core Numerics.Parametric

"""+definitions(chunk,7)
        text += '\ndef slabs : List (Slab 7) := ['+','.join(
            f'⟨I{i},C{i}⟩' for i in range(len(chunk)))+']\n'
        text += """
/-- Every real parameter in every listed slab has an actual unique source root. -/
theorem accepted : allCorrelatedAccepted P5.system slabs {precision:=-80}=true := by
  kernel_decide

"""+f'end polyak.Certificates.Continuation.P5.{name}\n'
        result[f'polyak/Certificates/Continuation/P5Batches/{name}.lean'] = text
    names = [f'Batch{i:03d}' for i in range(len(chunks))]
    text = ''.join(f'import polyak.Certificates.Continuation.P5Batches.{name}\n'
                   for name in names)
    text += """
/-! Article: Appendix B P5 continuation, complete closed-interval root coverage. -/
namespace polyak.Certificates.Continuation.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

"""
    expression = names[-1]+'.slabs'
    proof = names[-1]+'.accepted'
    for name in reversed(names[:-1]):
        expression = f'({name}.slabs ++ {expression})'
        proof = f'(allCorrelatedAccepted_append {name}.accepted {proof})'
    text += f'def slabs : List (Slab 7) := {expression}\n\n'
    text += f'theorem accepted : allCorrelatedAccepted system slabs {{precision:=-80}}=true :=\n  {proof}\n\n'
    text += """/-- Actual rational endpoints cover the entire claimed closed parameter domain. -/
theorem covered : coverCheck 0 (11791/500000) slabs=true := by kernel_decide

/-- Existence and box-local uniqueness for the actual, independently defined P5 system. -/
theorem source_roots {z : ℝ} (hz : z∈Set.Icc (0 : ℝ) (11791/500000)) :
    ∃ slab∈slabs, z∈slab.domain ∧ ∃! x,
      FinBoxMem x (coordinateBox slab.certificate.center slab.certificate.radius) ∧
        Boundary.P5.regularSystem (z,x)=0 := by
  obtain ⟨slab,hmem,hz,hroot⟩ := correlatedCover_roots system slabs {precision:=-80}
    0 (11791/500000) covered accepted (s:=z) (by norm_num at *; exact hz)
  exact ⟨slab,hmem,hz,by simpa only [source_system] using hroot⟩

end polyak.Certificates.Continuation.P5
"""
    result['polyak/Certificates/Continuation/P5Cover.lean'] = text
    return result


def generate_all(root=None):
    records = coarsen('p1', P1_LAYOUT)
    files = p1_batches(records)
    for path, text in files.items():
        lean_path(root,path).write_text(text, encoding='utf-8')
    return list(files)


def generate_central(root=None):
    files = central_batches(coarsen('central',CENTRAL_LAYOUT))
    for path,text in files.items():
        lean_path(root,path).write_text(text,encoding='utf-8')
    return list(files)


def central_links(count):
    """Endpoint proposals; each transfer is separately checked by the kernel."""
    files = {}
    for index in range(count-1):
        name = f'Link{index:03d}'
        left, right = f'Batch{index:03d}', f'Batch{index+1:03d}'
        files[f'polyak/Certificates/Continuation/P5Links/{name}.lean'] = f'''import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.{left}
import polyak.Certificates.Continuation.P5Batches.{right}

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer {index}. -/
namespace polyak.Certificates.Continuation.P5.{name}
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system {left}.C0 {right}.C0
    {left}.I0.hi {{precision:=-80}}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.{name}
'''
    names = [f'Batch{i:03d}' for i in range(count)]
    links = [f'Link{i:03d}' for i in range(count-1)]
    text = 'import polyak.Numerics.Parametric.ChainFamily\n'
    text += 'import polyak.Certificates.Continuation.P5Cover\n'
    text += ''.join(f'import polyak.Certificates.Continuation.P5Links.{name}\n'
                    for name in links)
    text += '''
/-! Article: Appendix B P5 continuation, compatible complete finite chain. -/
namespace polyak.Certificates.Continuation.P5
open LeanCert.Core Numerics.Parametric

'''
    text += f'def table : Fin {count} → Slab 7 := !['+','.join(
        f'⟨{name}.I0,{name}.C0⟩' for name in names)+']\n\n'
    text += 'theorem table_list : List.ofFn table=slabs := by rfl\n\n'
    text += 'theorem chain : ChainFamily system {precision:=-80} table where\n'
    text += '  checked := by\n    intro i\n    fin_cases i\n'
    for name in names:
        text += f'    · change checkCorrelated system {name}.I0 {name}.C0 {{precision:=-80}}=true\n'
        text += f'      simpa only [allCorrelatedAccepted,{name}.slabs,List.all_cons,List.all_nil,Bool.and_true] using {name}.accepted\n'
    text += '  seam := by kernel_decide\n  gap := by kernel_decide\n'
    text += '  linked := by\n    intro i\n    fin_cases i\n'
    for name in links:
        index = int(name[4:])
        left, right = names[index], names[index+1]
        text += f'    · change checkCorrelatedEndpoint system {left}.C0 {right}.C0 {left}.I0.hi {{precision:=-80}}=true\n'
        text += f'      exact {name}.accepted\n'
    text += '\nend polyak.Certificates.Continuation.P5\n'
    files['polyak/Certificates/Continuation/P5Family.lean'] = text
    return files


def generate_central_links(root=None):
    files = central_links(len(CENTRAL_LAYOUT))
    for path,text in files.items():
        lean_path(root,path).write_text(text,encoding='utf-8')
    return list(files)
