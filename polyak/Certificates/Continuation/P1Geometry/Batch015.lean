import polyak.Certificates.Continuation.P1Batches.Batch015
import polyak.Boundary.P1.SlabGeometry

/-! Article: (p1physical), finite scalar reserves on the source-linked P1 boxes. -/
namespace polyak.Certificates.Continuation.P1.Geometry.Batch015
open LeanCert.Core Numerics.Parametric Boundary.P1

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core0 : coreCheck P1.Batch015.I0 P1.Batch015.C0 {precision:=-80}=true := by kernel_decide

/-- The atom inequality on the prefix away from the exact junction. -/
theorem atom0 : atomCheck P1.Batch015.I0 P1.Batch015.C0 {precision:=-80}=true := by kernel_decide

/-- Actual implicit-derivative sign on the final endpoint neighborhood. -/
theorem slope0 : geometrySlopeCheck P1.system P1.Batch015.I0
    (coordinateBox P1.Batch015.C0.center P1.Batch015.C0.radius) {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core1 : coreCheck P1.Batch015.I1 P1.Batch015.C1 {precision:=-80}=true := by kernel_decide

/-- Actual implicit-derivative sign on the final endpoint neighborhood. -/
theorem slope1 : geometrySlopeCheck P1.system P1.Batch015.I1
    (coordinateBox P1.Batch015.C1.center P1.Batch015.C1.radius) {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core2 : coreCheck P1.Batch015.I2 P1.Batch015.C2 {precision:=-80}=true := by kernel_decide

/-- Actual implicit-derivative sign on the final endpoint neighborhood. -/
theorem slope2 : geometrySlopeCheck P1.system P1.Batch015.I2
    (coordinateBox P1.Batch015.C2.center P1.Batch015.C2.radius) {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core3 : coreCheck P1.Batch015.I3 P1.Batch015.C3 {precision:=-80}=true := by kernel_decide

/-- Actual implicit-derivative sign on the final endpoint neighborhood. -/
theorem slope3 : geometrySlopeCheck P1.system P1.Batch015.I3
    (coordinateBox P1.Batch015.C3.center P1.Batch015.C3.radius) {precision:=-80}=true := by kernel_decide

/-- Scalar core reserves; the tight endpoint atom inequality is handled separately. -/
theorem core4 : coreCheck P1.Batch015.I4 P1.Batch015.C4 {precision:=-80}=true := by kernel_decide

/-- Actual implicit-derivative sign on the final endpoint neighborhood. -/
theorem slope4 : geometrySlopeCheck P1.system P1.Batch015.I4
    (coordinateBox P1.Batch015.C4.center P1.Batch015.C4.radius) {precision:=-80}=true := by kernel_decide

theorem coreAccepted : allCoreCheck P1.Batch015.slabs {precision:=-80}=true := by
  simp only [allCoreCheck,P1.Batch015.slabs,List.all_cons,List.all_nil,core0,core1,core2,core3,core4,Bool.and_true]

def atomSlabs : List (Slab 2) := [⟨P1.Batch015.I0,P1.Batch015.C0⟩]

theorem atomAccepted : allAtomCheck atomSlabs {precision:=-80}=true := by
  simp only [allAtomCheck,atomSlabs,List.all_cons,List.all_nil,atom0,Bool.and_true]

theorem slopeAccepted : allSlopeCheck P1.system P1.Batch015.slabs {precision:=-80}=true := by
  simp only [allSlopeCheck,P1.Batch015.slabs,List.all_cons,List.all_nil,slope0,slope1,slope2,slope3,slope4,Bool.and_true]

end polyak.Certificates.Continuation.P1.Geometry.Batch015
