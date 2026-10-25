import polyak.Certificates.Continuation.P1Batches.Batch013
import polyak.Boundary.P1.SlabDerivative

/-! Article: Proposition P1, actual strict derivative reserves on the accepted source cover. -/
namespace polyak.Certificates.Continuation.P1.Slope.Batch013
open LeanCert.Core Numerics.Parametric Boundary.P1

theorem slope0 : sourceSlopeCheck P1.system P1.Batch013.I0
    (coordinateBox P1.Batch013.C0.center P1.Batch013.C0.radius) {precision:=-80}=true := by kernel_decide

theorem slope1 : sourceSlopeCheck P1.system P1.Batch013.I1
    (coordinateBox P1.Batch013.C1.center P1.Batch013.C1.radius) {precision:=-80}=true := by kernel_decide

theorem slope2 : sourceSlopeCheck P1.system P1.Batch013.I2
    (coordinateBox P1.Batch013.C2.center P1.Batch013.C2.radius) {precision:=-80}=true := by kernel_decide

theorem slope3 : sourceSlopeCheck P1.system P1.Batch013.I3
    (coordinateBox P1.Batch013.C3.center P1.Batch013.C3.radius) {precision:=-80}=true := by kernel_decide

theorem slope4 : sourceSlopeCheck P1.system P1.Batch013.I4
    (coordinateBox P1.Batch013.C4.center P1.Batch013.C4.radius) {precision:=-80}=true := by kernel_decide

theorem slope5 : sourceSlopeCheck P1.system P1.Batch013.I5
    (coordinateBox P1.Batch013.C5.center P1.Batch013.C5.radius) {precision:=-80}=true := by kernel_decide

theorem slope6 : sourceSlopeCheck P1.system P1.Batch013.I6
    (coordinateBox P1.Batch013.C6.center P1.Batch013.C6.radius) {precision:=-80}=true := by kernel_decide

theorem slope7 : sourceSlopeCheck P1.system P1.Batch013.I7
    (coordinateBox P1.Batch013.C7.center P1.Batch013.C7.radius) {precision:=-80}=true := by kernel_decide

theorem slope8 : sourceSlopeCheck P1.system P1.Batch013.I8
    (coordinateBox P1.Batch013.C8.center P1.Batch013.C8.radius) {precision:=-80}=true := by kernel_decide

theorem slope9 : sourceSlopeCheck P1.system P1.Batch013.I9
    (coordinateBox P1.Batch013.C9.center P1.Batch013.C9.radius) {precision:=-80}=true := by kernel_decide

theorem accepted : allSourceSlopeCheck P1.system P1.Batch013.slabs {precision:=-80}=true := by
  simp only [allSourceSlopeCheck,P1.Batch013.slabs,List.all_cons,List.all_nil,slope0,slope1,slope2,slope3,slope4,slope5,slope6,slope7,slope8,slope9,Bool.and_true]

end polyak.Certificates.Continuation.P1.Slope.Batch013
