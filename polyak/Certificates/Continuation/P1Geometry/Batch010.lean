import polyak.Certificates.Continuation.P1Batches.Batch010
import polyak.Boundary.P1.SlabGeometry

/-! Article: (p1physical), finite scalar reserves on the source-linked P1 boxes. -/
namespace polyak.Certificates.Continuation.P1.Geometry.Batch010
open LeanCert.Core Numerics.Parametric Boundary.P1

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core0 : coreCheck P1.Batch010.I0 P1.Batch010.C0 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom0 : atomCheck P1.Batch010.I0 P1.Batch010.C0 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core1 : coreCheck P1.Batch010.I1 P1.Batch010.C1 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom1 : atomCheck P1.Batch010.I1 P1.Batch010.C1 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core2 : coreCheck P1.Batch010.I2 P1.Batch010.C2 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom2 : atomCheck P1.Batch010.I2 P1.Batch010.C2 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core3 : coreCheck P1.Batch010.I3 P1.Batch010.C3 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom3 : atomCheck P1.Batch010.I3 P1.Batch010.C3 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core4 : coreCheck P1.Batch010.I4 P1.Batch010.C4 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom4 : atomCheck P1.Batch010.I4 P1.Batch010.C4 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core5 : coreCheck P1.Batch010.I5 P1.Batch010.C5 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom5 : atomCheck P1.Batch010.I5 P1.Batch010.C5 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core6 : coreCheck P1.Batch010.I6 P1.Batch010.C6 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom6 : atomCheck P1.Batch010.I6 P1.Batch010.C6 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core7 : coreCheck P1.Batch010.I7 P1.Batch010.C7 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom7 : atomCheck P1.Batch010.I7 P1.Batch010.C7 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core8 : coreCheck P1.Batch010.I8 P1.Batch010.C8 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom8 : atomCheck P1.Batch010.I8 P1.Batch010.C8 {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core9 : coreCheck P1.Batch010.I9 P1.Batch010.C9 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom9 : atomCheck P1.Batch010.I9 P1.Batch010.C9 {precision:=-80}=true := by kernel_decide

theorem coreAccepted : allCoreCheck P1.Batch010.slabs {precision:=-80}=true := by
  simp only [allCoreCheck,P1.Batch010.slabs,List.all_cons,List.all_nil,core0,core1,core2,core3,core4,core5,core6,core7,core8,core9,Bool.and_true]

def atomSlabs : List (Slab 2) := [⟨P1.Batch010.I0,P1.Batch010.C0⟩,⟨P1.Batch010.I1,P1.Batch010.C1⟩,⟨P1.Batch010.I2,P1.Batch010.C2⟩,⟨P1.Batch010.I3,P1.Batch010.C3⟩,⟨P1.Batch010.I4,P1.Batch010.C4⟩,⟨P1.Batch010.I5,P1.Batch010.C5⟩,⟨P1.Batch010.I6,P1.Batch010.C6⟩,⟨P1.Batch010.I7,P1.Batch010.C7⟩,⟨P1.Batch010.I8,P1.Batch010.C8⟩,⟨P1.Batch010.I9,P1.Batch010.C9⟩]

theorem atomAccepted : allAtomCheck atomSlabs {precision:=-80}=true := by
  simp only [allAtomCheck,atomSlabs,List.all_cons,List.all_nil,atom0,atom1,atom2,atom3,atom4,atom5,atom6,atom7,atom8,atom9,Bool.and_true]

end polyak.Certificates.Continuation.P1.Geometry.Batch010
