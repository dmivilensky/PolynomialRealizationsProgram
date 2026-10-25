import polyak.Certificates.Continuation.P1Batches.Batch015
import polyak.Boundary.P1.SlabDerivative

/-! Article: Proposition P1, actual strict derivative reserves on the accepted source cover. -/
namespace polyak.Certificates.Continuation.P1.Slope.Batch015
open LeanCert.Core Numerics.Parametric Boundary.P1

theorem slope0 : sourceSlopeCheck P1.system P1.Batch015.I0
    (coordinateBox P1.Batch015.C0.center P1.Batch015.C0.radius) {precision:=-80}=true := by kernel_decide

theorem slope1 : sourceSlopeCheck P1.system P1.Batch015.I1
    (coordinateBox P1.Batch015.C1.center P1.Batch015.C1.radius) {precision:=-80}=true := by kernel_decide

theorem slope2 : sourceSlopeCheck P1.system P1.Batch015.I2
    (coordinateBox P1.Batch015.C2.center P1.Batch015.C2.radius) {precision:=-80}=true := by kernel_decide

theorem slope3 : sourceSlopeCheck P1.system P1.Batch015.I3
    (coordinateBox P1.Batch015.C3.center P1.Batch015.C3.radius) {precision:=-80}=true := by kernel_decide

theorem slope4 : sourceSlopeCheck P1.system P1.Batch015.I4
    (coordinateBox P1.Batch015.C4.center P1.Batch015.C4.radius) {precision:=-80}=true := by kernel_decide

theorem accepted : allSourceSlopeCheck P1.system P1.Batch015.slabs {precision:=-80}=true := by
  simp only [allSourceSlopeCheck,P1.Batch015.slabs,List.all_cons,List.all_nil,slope0,slope1,slope2,slope3,slope4,Bool.and_true]

end polyak.Certificates.Continuation.P1.Slope.Batch015
