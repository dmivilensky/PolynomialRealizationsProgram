import polyak.Boundary.P1.Selection
import polyak.Boundary.P1.LocalGluing
import polyak.Boundary.P1.EndpointAdmissible
import polyak.Certificates.Continuation.P1Geometry
import polyak.Numerics.Parametric.ImplicitDerivative

/-!
Article: the complete regular P1 continuation on [0,733/1000].
Use: source-linked checked boxes give roots and scalar reserves; strict quartic
monotonicity glues their analytic IFT extensions without any assumed selection continuity.
-/
noncomputable section
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric Filter
open scoped Topology

theorem continuation_core {z : ℝ} (hz : z∈continuationDomain) : CoreBounds z (continuation z) := by
  let p := checkedPoint z hz
  have hc := allCoreCheck_sound polyak.Certificates.Continuation.P1.Geometry.coreAccepted
    p.mem hz.1 p.parameter p.box
  rwa [← continuation_eq_point hz] at hc

theorem continuation_admissible {z : ℝ} (hz : z∈continuationDomain) :
    ContactAdmissible (z,continuation z) :=
  coreRoot_admissible hz.1 (by have h:=hz.2; change z≤733/1000 at h; linarith)
    (continuation_source hz) (continuation_core hz)

theorem continuation_local_agreement {z : ℝ} (hz : z∈continuationDomain) :
    ∃ g : ℝ → Coordinates, AnalyticAt ℝ g z ∧ g z=continuation z ∧
      ∀ᶠ r in 𝓝 z, r∈continuationDomain → continuation r=g r := by
  obtain ⟨g,hg,hself,heq⟩ := continuation_local_extension hz
  refine ⟨g,hg,hself,local_extension_unique ?_ (fun _ hr => continuation_source hr)
    (fun _ hr => continuation_admissible hr) hz hg hself heq⟩
  intro r hr
  exact ⟨hr.1,by have h:=hr.2; change r≤733/1000 at h; linarith⟩

theorem continuation_analyticWithinAt {z : ℝ} (hz : z∈continuationDomain) :
    AnalyticWithinAt ℝ continuation continuationDomain z := by
  obtain ⟨g,hg,hself,heq⟩ := continuation_local_agreement hz
  apply hg.analyticWithinAt.congr_of_eventuallyEq _ hself.symm
  filter_upwards [heq.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hrS
  exact hr hrS

theorem continuation_continuousOn : ContinuousOn continuation continuationDomain :=
  fun _ hz => (continuation_analyticWithinAt hz).continuousWithinAt

theorem continuation_analyticAt {z : ℝ} (hz : z∈Set.Ioo (0 : ℝ) (733/1000)) :
    AnalyticAt ℝ continuation z := by
  obtain ⟨g,hg,_,heq⟩ := continuation_local_agreement ⟨hz.1.le,hz.2.le⟩
  apply hg.congr
  filter_upwards [heq,Icc_mem_nhds hz.1 hz.2] with r hr hrS
  exact (hr hrS).symm

/-- The entire checked branch has the actual regular IFT expansion at the critical endpoint. -/
theorem continuation_eq_localBranch :
    ∀ᶠ z in 𝓝 (0 : ℝ), z∈continuationDomain → continuation z=localBranch z := by
  apply eq_localBranch_eventually ?_ (fun _ hz => continuation_source hz)
    (fun _ hz => continuation_admissible hz) (by norm_num [continuationDomain])
  intro z hz
  exact ⟨hz.1,by have h:=hz.2; change z≤733/1000 at h; linarith⟩

theorem zW_mem_continuationDomain : zW∈continuationDomain :=
  ⟨zW_pos.le,zW_bounds.2.le⟩

/-- The exact spiral point identifies the continued endpoint by algebraic uniqueness alone. -/
theorem continuation_endpoint : continuation zW=endpoint :=
  admissibleRoot_unique zW_pos.le (by linarith [zW_bounds.2])
    (continuation_source zW_mem_continuationDomain) endpoint_regularSystem
    (continuation_admissible zW_mem_continuationDomain) endpoint_admissible

theorem continuation_mem_box {z : ℝ} (hz : z∈continuationDomain) {slab : Slab 2}
    (hm : slab∈polyak.Certificates.Continuation.P1.slabs) (hs : z∈slab.domain) :
    FinBoxMem (continuation z) (coordinateBox slab.certificate.center slab.certificate.radius) := by
  have hc : checkDyadic polyak.Certificates.Continuation.P1.system slab.domain slab.certificate
      {precision:=-80}=true := List.all_eq_true.mp polyak.Certificates.Continuation.P1.accepted slab hm
  obtain ⟨x,hx,_⟩ := checkDyadic_sound polyak.Certificates.Continuation.P1.system
    slab.domain slab.certificate {precision:=-80} hc z hs
  have hxs : regularSystem (z,x)=0 := by
    simpa only [polyak.Certificates.Continuation.P1.source_system] using hx.2
  have hxb := allCoreCheck_sound polyak.Certificates.Continuation.P1.Geometry.coreAccepted hm hz.1 hs hx.1
  have he : continuation z=x := admissibleRoot_unique hz.1
    (by have h:=hz.2; change z≤733/1000 at h; linarith) (continuation_source hz) hxs
    (continuation_admissible hz) (coreRoot_admissible hz.1
      (by have h:=hz.2; change z≤733/1000 at h; linarith) hxs hxb)
  rw [he]
  exact hx.1

theorem continuation_derivative_equation {z : ℝ} (hz : z∈Set.Ioo (0 : ℝ) (733/1000)) :
    (jacobian polyak.Certificates.Continuation.P1.system z (continuation z)).mulVec (deriv continuation z)=
      -parameterDerivative polyak.Certificates.Continuation.P1.system z (continuation z) := by
  apply implicit_derivative polyak.Certificates.Continuation.P1.system
    (fun i => ((polyak.Certificates.Continuation.P1.system i).checkADSupported_eq_true_iff).mp
      (polyak.Certificates.Continuation.P1.check_supported i)) (continuation_analyticAt hz).differentiableAt
  filter_upwards [Icc_mem_nhds hz.1 hz.2] with r hr
  rw [polyak.Certificates.Continuation.P1.source_system]
  exact continuation_source hr

end polyak.Boundary.P1
