import polyak.Boundary.P5.DerivativeSource
import polyak.Certificates.Continuation.P5Slope

/-! Article: central-family derivatives on the actual globally selected source
branch, with every strict reserve supplied by a checked AD enclosure. -/
namespace polyak.Boundary.P5
noncomputable section
open LeanCert.Core LeanCert.Engine Numerics.Parametric Filter Set
open scoped Topology

/-- Actual derivative reserves at every point of the open checked continuation domain. -/
theorem continuation_derivative_bounds {h : ℝ} (hh : h∈Ioo (0 : ℝ) (11791/500000)) :
    |Selection.continuation h 0+h*deriv Selection.continuation h 0|<1 ∧
      0<deriv Selection.continuation h 5+deriv Selection.continuation h 6 := by
  have hcover : h∈Icc (((0 : ℚ) : ℝ)) (((11791/500000 : ℚ) : ℝ)) := by
    norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat]
    exact ⟨hh.1.le,hh.2.le⟩
  obtain ⟨slab,hmem,hs⟩:=coverCheck_sound Certificates.Continuation.P5.slabs 0 (11791/500000)
    Certificates.Continuation.P5.covered hcover
  rw [←Certificates.Continuation.P5.table_list] at hmem
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hmem
  obtain ⟨J,p,henc,hcheck⟩:=Certificates.Continuation.P5.Slope.checked i
  exact sourceSlopeCheck_sound _
    (fun k => ((Certificates.Continuation.P5.system k).checkADSupported_eq_true_iff).mp
      (Certificates.Continuation.P5.check_supported k)) _ _ _ _ J p _ henc hcheck hs
    (Selection.continuation_mem i hs) (continuation_derivative_equation hh)

theorem continuationWeight5_strictAntiOn :
    StrictAntiOn continuationWeight5 (Icc (0 : ℝ) (11791/500000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact continuationWeight5_continuousOn
  · intro h hh
    have hho : h∈Ioo (0 : ℝ) (11791/500000) := by simpa only [interior_Icc] using hh
    rw [(continuationWeight5_hasDerivAt hho).deriv]
    linarith [(continuation_derivative_bounds hho).2]

end
end polyak.Boundary.P5
