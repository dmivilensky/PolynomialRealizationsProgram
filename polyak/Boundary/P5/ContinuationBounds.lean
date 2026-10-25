import polyak.Boundary.P5.Selection
import polyak.Certificates.Continuation.P5Properties

/-! All finite and infinite reserves for the actual globally selected P5 source branch. -/
noncomputable section
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

/-- Every selected value lies in one of the actual accepted source boxes. -/
theorem continuation_checkedBox {h : ℝ} (hh : h∈Set.Icc (0 : ℝ) (11791/500000)) :
    ∃ slab∈Certificates.Continuation.P5.slabs,h∈slab.domain ∧
      FinBoxMem (Selection.continuation h)
        (coordinateBox slab.certificate.center slab.certificate.radius) := by
  obtain ⟨slab,hm,hs⟩ := coverCheck_sound Certificates.Continuation.P5.slabs 0 (11791/500000)
    Certificates.Continuation.P5.covered (s:=h) (by norm_num at *; exact hh)
  refine ⟨slab,hm,hs,?_⟩
  rw [← Certificates.Continuation.P5.table_list] at hm
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
  exact Selection.continuation_mem i hs

/-- All 25 scalar and residual reserves refer to the actual source branch. -/
theorem continuation_geometry {h : ℝ} (hh : h∈Set.Ioc (0 : ℝ) (11791/500000)) :
    ContinuationGeometry h (Selection.continuation h) := by
  obtain ⟨slab,hm,hs,hX⟩ := continuation_checkedBox ⟨hh.1.le,hh.2⟩
  exact allGeometryCheck_sound Certificates.Continuation.P5Properties.geometryAccepted hm
    hh.1 (by linarith [hh.2]) hs hX

/-- All original finite constraints, including the four exactly active source equations. -/
theorem continuation_prefix {h : ℝ} (hh : h∈Set.Icc (0 : ℝ) (11791/500000)) :
    ∀ n : ℕ, 1≤n → n<24 → ∀ σ : ℝ, (σ= -1 ∨ σ=1) →
      0≤actualPrimal h (Selection.continuation h) n σ := by
  obtain ⟨slab,hm,hs,hX⟩ := continuation_checkedBox hh
  exact allPrefixCheck_sound Certificates.Continuation.P5Lags.codes
    Certificates.Continuation.P5Properties.prefixAccepted hm hh.1 hs hX (Selection.continuation_source hh)

end polyak.Boundary.P5
