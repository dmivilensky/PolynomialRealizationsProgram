import polyak.Certificates.Continuation.P5Batches.Batch000
import polyak.Certificates.Continuation.P5Batches.Batch001
import polyak.Certificates.Continuation.P5Batches.Batch002
import polyak.Certificates.Continuation.P5Batches.Batch003
import polyak.Certificates.Continuation.P5Batches.Batch004
import polyak.Certificates.Continuation.P5Batches.Batch005
import polyak.Certificates.Continuation.P5Batches.Batch006
import polyak.Certificates.Continuation.P5Batches.Batch007
import polyak.Certificates.Continuation.P5Batches.Batch008
import polyak.Certificates.Continuation.P5Batches.Batch009
import polyak.Certificates.Continuation.P5Batches.Batch010
import polyak.Certificates.Continuation.P5Batches.Batch011
import polyak.Certificates.Continuation.P5Batches.Batch012
import polyak.Certificates.Continuation.P5Batches.Batch013
import polyak.Certificates.Continuation.P5Batches.Batch014
import polyak.Certificates.Continuation.P5Batches.Batch015
import polyak.Certificates.Continuation.P5Batches.Batch016
import polyak.Certificates.Continuation.P5Batches.Batch017
import polyak.Certificates.Continuation.P5Batches.Batch018
import polyak.Certificates.Continuation.P5Batches.Batch019

/-! Article: Appendix B P5 continuation, complete closed-interval root coverage. -/
namespace polyak.Certificates.Continuation.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def slabs : List (Slab 7) := (Batch000.slabs ++ (Batch001.slabs ++ (Batch002.slabs ++ (Batch003.slabs ++ (Batch004.slabs ++ (Batch005.slabs ++ (Batch006.slabs ++ (Batch007.slabs ++ (Batch008.slabs ++ (Batch009.slabs ++ (Batch010.slabs ++ (Batch011.slabs ++ (Batch012.slabs ++ (Batch013.slabs ++ (Batch014.slabs ++ (Batch015.slabs ++ (Batch016.slabs ++ (Batch017.slabs ++ (Batch018.slabs ++ Batch019.slabs)))))))))))))))))))

theorem accepted : allCorrelatedAccepted system slabs {precision:=-80}=true :=
  (allCorrelatedAccepted_append Batch000.accepted (allCorrelatedAccepted_append Batch001.accepted (allCorrelatedAccepted_append Batch002.accepted (allCorrelatedAccepted_append Batch003.accepted (allCorrelatedAccepted_append Batch004.accepted (allCorrelatedAccepted_append Batch005.accepted (allCorrelatedAccepted_append Batch006.accepted (allCorrelatedAccepted_append Batch007.accepted (allCorrelatedAccepted_append Batch008.accepted (allCorrelatedAccepted_append Batch009.accepted (allCorrelatedAccepted_append Batch010.accepted (allCorrelatedAccepted_append Batch011.accepted (allCorrelatedAccepted_append Batch012.accepted (allCorrelatedAccepted_append Batch013.accepted (allCorrelatedAccepted_append Batch014.accepted (allCorrelatedAccepted_append Batch015.accepted (allCorrelatedAccepted_append Batch016.accepted (allCorrelatedAccepted_append Batch017.accepted (allCorrelatedAccepted_append Batch018.accepted Batch019.accepted)))))))))))))))))))

/-- Actual rational endpoints cover the entire claimed closed parameter domain. -/
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
