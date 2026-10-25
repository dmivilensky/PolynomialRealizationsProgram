import polyak.Certificates.Continuation.P1Batches.Batch000
import polyak.Certificates.Continuation.P1Batches.Batch001
import polyak.Certificates.Continuation.P1Batches.Batch002
import polyak.Certificates.Continuation.P1Batches.Batch003
import polyak.Certificates.Continuation.P1Batches.Batch004
import polyak.Certificates.Continuation.P1Batches.Batch005
import polyak.Certificates.Continuation.P1Batches.Batch006
import polyak.Certificates.Continuation.P1Batches.Batch007
import polyak.Certificates.Continuation.P1Batches.Batch008
import polyak.Certificates.Continuation.P1Batches.Batch009
import polyak.Certificates.Continuation.P1Batches.Batch010
import polyak.Certificates.Continuation.P1Batches.Batch011
import polyak.Certificates.Continuation.P1Batches.Batch012
import polyak.Certificates.Continuation.P1Batches.Batch013
import polyak.Certificates.Continuation.P1Batches.Batch014
import polyak.Certificates.Continuation.P1Batches.Batch015

/-! Article: Appendix B P1 continuation, complete closed-interval root coverage. -/
namespace polyak.Certificates.Continuation.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def slabs : List (Slab 2) := (Batch000.slabs ++ (Batch001.slabs ++ (Batch002.slabs ++ (Batch003.slabs ++ (Batch004.slabs ++ (Batch005.slabs ++ (Batch006.slabs ++ (Batch007.slabs ++ (Batch008.slabs ++ (Batch009.slabs ++ (Batch010.slabs ++ (Batch011.slabs ++ (Batch012.slabs ++ (Batch013.slabs ++ (Batch014.slabs ++ Batch015.slabs)))))))))))))))

theorem accepted : allAccepted system slabs {precision:=-80}=true :=
  (allAccepted_append Batch000.accepted (allAccepted_append Batch001.accepted (allAccepted_append Batch002.accepted (allAccepted_append Batch003.accepted (allAccepted_append Batch004.accepted (allAccepted_append Batch005.accepted (allAccepted_append Batch006.accepted (allAccepted_append Batch007.accepted (allAccepted_append Batch008.accepted (allAccepted_append Batch009.accepted (allAccepted_append Batch010.accepted (allAccepted_append Batch011.accepted (allAccepted_append Batch012.accepted (allAccepted_append Batch013.accepted (allAccepted_append Batch014.accepted Batch015.accepted)))))))))))))))

/-- Actual rational endpoints cover the entire claimed closed parameter domain. -/
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
