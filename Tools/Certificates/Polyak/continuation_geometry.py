"""Exact scalar annotations for the fixed source-linked P1 continuation layout.

The archive supplies only the existing accepted root slab data.  The local
consumer emits kernel checks of the independent source inequalities; producer
success flags do not enter any theorem.
"""
from .Payload import interval_proposals
from .continuation_boxes import P1_LAYOUT, coarsen
from .paths import lean_path


def output_names():
    return [f'polyak/Certificates/Continuation/P1Geometry/Batch{i:03d}.lean'
            for i in range((len(P1_LAYOUT)+9)//10)]+[
                'polyak/Certificates/Continuation/P1Geometry.lean']


def generate(root=None):
    records=coarsen('p1',P1_LAYOUT)
    # Validate the exact archived layout contract before referring to its Lean constants.
    if interval_proposals('p1')['unknown_order'] != ['A','B'] or len(records) != 155:
        raise ValueError('unexpected P1 continuation geometry layout')
    files={}
    chunks=[records[i:i+10] for i in range(0,len(records),10)]
    for b,chunk in enumerate(chunks):
        label=f'Batch{b:03d}'
        text=f'''import polyak.Certificates.Continuation.P1Batches.{label}
import polyak.Boundary.P1.SlabGeometry

/-! Article: (p1physical), finite scalar reserves on the source-linked P1 boxes. -/
namespace polyak.Certificates.Continuation.P1.Geometry.{label}
open LeanCert.Core Numerics.Parametric Boundary.P1

'''
        core_names=[]
        atom_names=[]
        slope_names=[]
        for j in range(len(chunk)):
            text+=f'''/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core{j} : coreCheck B.I{j} B.C{j} {{precision:=-80}}=true := by kernel_decide

'''
            core_names.append(f'core{j}')
            if 10*b+j < 151:
                text+=f'''/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom{j} : atomCheck B.I{j} B.C{j} {{precision:=-80}}=true := by kernel_decide

'''
                atom_names.append(f'atom{j}')
            if b == len(chunks)-1:
                text+=f'''/-- Actual implicit-derivative sign on the final endpoint neighborhood. -/
theorem slope{j} : geometrySlopeCheck P1.system B.I{j}
    (coordinateBox B.C{j}.center B.C{j}.radius) {{precision:=-80}}=true := by kernel_decide

'''
                slope_names.append(f'slope{j}')
        text+='theorem coreAccepted : allCoreCheck B.slabs {precision:=-80}=true := by\n'
        text+='  simp only [allCoreCheck,B.slabs,List.all_cons,List.all_nil,'+','.join(core_names)+',Bool.and_true]\n\n'
        atom_count=len(atom_names)
        text+='def atomSlabs : List (Slab 2) := ['+','.join(f'⟨B.I{j},B.C{j}⟩' for j in range(atom_count))+']\n\n'
        text+='theorem atomAccepted : allAtomCheck atomSlabs {precision:=-80}=true := by\n'
        text+='  simp only [allAtomCheck,atomSlabs,List.all_cons,List.all_nil,'+','.join(atom_names)+',Bool.and_true]\n\n'
        if slope_names:
            text+='theorem slopeAccepted : allSlopeCheck P1.system B.slabs {precision:=-80}=true := by\n'
            text+='  simp only [allSlopeCheck,B.slabs,List.all_cons,List.all_nil,'+','.join(slope_names)+',Bool.and_true]\n\n'
        text+=f'end polyak.Certificates.Continuation.P1.Geometry.{label}\n'
        text=text.replace('B.',f'P1.{label}.')
        files[f'polyak/Certificates/Continuation/P1Geometry/{label}.lean']=text
    names=[f'Batch{i:03d}' for i in range(len(chunks))]
    text=''.join(f'import polyak.Certificates.Continuation.P1Geometry.{name}\n' for name in names)
    text+='''import polyak.Certificates.Continuation.P1Cover

/-! Article: complete scalar reserves and the endpoint neighborhood on the P1 source cover. -/
namespace polyak.Certificates.Continuation.P1.Geometry
open LeanCert.Core Numerics.Parametric Boundary.P1

'''
    core_proof=names[-1]+'.coreAccepted'
    atom_proof=names[-1]+'.atomAccepted'
    atom_expr=names[-1]+'.atomSlabs'
    for name in reversed(names[:-1]):
        core_proof=f'(allCoreCheck_append {name}.coreAccepted {core_proof})'
        atom_proof=f'(allAtomCheck_append {name}.atomAccepted {atom_proof})'
        atom_expr=f'({name}.atomSlabs++{atom_expr})'
    text+=f'theorem coreAccepted : allCoreCheck P1.slabs {{precision:=-80}}=true :=\n  {core_proof}\n\n'
    text+=f'def atomSlabs : List (Slab 2) := {atom_expr}\n\n'
    text+=f'theorem atomAccepted : allAtomCheck atomSlabs {{precision:=-80}}=true :=\n  {atom_proof}\n\n'
    text+='theorem atomSlabs_subset {slab : Slab 2} (hm : slab∈atomSlabs) : slab∈P1.slabs := by\n'
    text+='  simp only [atomSlabs,List.mem_append] at hm\n'
    text+='  simp only [P1.slabs,List.mem_append]\n'
    text+='  rcases hm with '+' | '.join(f'h{i}' for i in range(len(chunks)))+'\n'
    for i in range(len(chunks)):
        proof=f'h{i}'
        if i == len(chunks)-1:
            text+='  · '+('right; '*i)+'\n'
            text+=f'    simp only [Batch015.atomSlabs,List.mem_cons,List.not_mem_nil,or_false] at h{i}\n'
            text+=f'    subst slab\n    exact List.mem_cons_self\n'
        else:
            proof='Or.inl '+proof
            for _ in range(i):proof='Or.inr ('+proof+')'
            text+='  · exact '+proof+'\n'
    text+='\n' 
    end=records[150]['parameter'][1]
    start=records[150]['parameter'][0]
    text+=f'def prefixEnd : ℝ := ({end} : ℚ)\n\n'
    text+=f'theorem atomCovered : coverCheck 0 ({end}) atomSlabs=true := by kernel_decide\n\n'
    text+='def tailSlabs : List (Slab 2) := P1.Batch015.slabs\n\n'
    text+='theorem slopeAccepted : allSlopeCheck P1.system tailSlabs {precision:=-80}=true := Batch015.slopeAccepted\n\n'
    text+=f'theorem tailCovered : coverCheck ({start}) (733/1000) tailSlabs=true := by kernel_decide\n\n'
    text+='theorem tailSlabs_subset {slab : Slab 2} (hm : slab∈tailSlabs) : slab∈P1.slabs := by\n'
    text+='  simp only [P1.slabs,List.mem_append]\n'
    proof='hm'
    for _ in range(15):proof='Or.inr ('+proof+')'
    text+='  exact '+proof+'\n\n'
    text+='end polyak.Certificates.Continuation.P1.Geometry\n' 
    files['polyak/Certificates/Continuation/P1Geometry.lean']=text
    for path,text in files.items():
        lean_path(root,path).write_text(text,encoding='utf-8')
    return list(files)
