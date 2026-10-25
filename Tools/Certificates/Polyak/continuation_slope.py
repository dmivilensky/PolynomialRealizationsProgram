"""Source derivative checks on the fixed archive-driven P1 root slab cover.

Only existing mathematical interval data are consumed. The local Lean checker
recomputes actual AD derivatives, determinants and strict slope-square reserves.
No external pass flag or executed producer code is a theorem premise.
"""
from .Payload import interval_proposals
from .continuation_boxes import P1_LAYOUT, coarsen
from .paths import lean_path


def output_names():
    return [f'polyak/Certificates/Continuation/P1Slope/Batch{i:03d}.lean'
            for i in range((len(P1_LAYOUT)+9)//10)] + [
                'polyak/Certificates/Continuation/P1Slope.lean']


def generate(root=None):
    records = coarsen('p1', P1_LAYOUT)
    if interval_proposals('p1')['unknown_order'] != ['A', 'B'] or len(records) != 155:
        raise ValueError('unexpected P1 derivative slab contract')
    chunks = [records[i:i+10] for i in range(0, len(records), 10)]
    files = {}
    names = []
    for b, chunk in enumerate(chunks):
        label = f'Batch{b:03d}'
        names.append(label)
        text = f'''import polyak.Certificates.Continuation.P1Batches.{label}
import polyak.Boundary.P1.SlabDerivative

/-! Article: Proposition P1, actual strict derivative reserves on the accepted source cover. -/
namespace polyak.Certificates.Continuation.P1.Slope.{label}
open LeanCert.Core Numerics.Parametric Boundary.P1

'''
        proofs = []
        for j in range(len(chunk)):
            proofs.append(f'slope{j}')
            text += f'''theorem slope{j} : sourceSlopeCheck P1.system P1.{label}.I{j}
    (coordinateBox P1.{label}.C{j}.center P1.{label}.C{j}.radius) {{precision:=-80}}=true := by kernel_decide

'''
        text += f'theorem accepted : allSourceSlopeCheck P1.system P1.{label}.slabs {{precision:=-80}}=true := by\n'
        text += '  simp only [allSourceSlopeCheck,P1.' + label + '.slabs,List.all_cons,List.all_nil,'
        text += ','.join(proofs) + ',Bool.and_true]\n\n'
        text += f'end polyak.Certificates.Continuation.P1.Slope.{label}\n'
        files[f'polyak/Certificates/Continuation/P1Slope/{label}.lean'] = text
    text = ''.join(f'import polyak.Certificates.Continuation.P1Slope.{name}\n' for name in names)
    text += '''import polyak.Certificates.Continuation.P1Cover

/-! Article: Proposition P1, full closed-domain strict source slope verification. -/
namespace polyak.Certificates.Continuation.P1.Slope
open LeanCert.Core Numerics.Parametric Boundary.P1

'''
    proof = names[-1] + '.accepted'
    for name in reversed(names[:-1]):
        proof = f'(allSourceSlopeCheck_append {name}.accepted {proof})'
    text += 'theorem accepted : allSourceSlopeCheck P1.system P1.slabs {precision:=-80}=true :=\n  ' + proof + '\n\n'
    text += 'end polyak.Certificates.Continuation.P1.Slope\n'
    files['polyak/Certificates/Continuation/P1Slope.lean'] = text
    for path, content in files.items():
        lean_path(root, path).write_text(content, encoding='utf-8')
    return list(files)
