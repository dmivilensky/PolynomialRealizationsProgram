import polyak.Boundary.P1.PhysicalContinuation
import polyak.Boundary.P1.Derivative
import polyak.Certificates.Continuation.P1Slope

/-!
Article: Proposition P₁, actual derivative bounds on the whole checked physical arc.
Use: all 155 source slabs supply actual AD/Cramer bounds for the analytic continued
branch; the reciprocal-cosh chain then proves the actual optimal boundary slope.
-/
noncomputable section
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric Filter Set
open scoped Topology

/-- The actual globally continued P₁ twist in the reciprocal-cosh coordinate. -/
def continuedU (z : ℝ) : ℝ := branchU z (continuation z 0)

def continuedUDerivative (z : ℝ) : ℝ :=
  -1/2+2*z*continuation z 0+z^2*deriv continuation z 0

theorem continuedU_hasDerivAt {z : ℝ} (hz : z∈Ioo (0 : ℝ) (733/1000)) :
    HasDerivAt continuedU (continuedUDerivative z) z := by
  have hg:=(continuation_analyticAt hz).differentiableAt.hasDerivAt
  have hA:=(ContinuousLinearMap.proj (0 : Fin 2) : Coordinates →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z hg
  have hq:=hasDerivAt_id z
  have hh:=((hasDerivAt_const z (1 : ℝ)).sub (hq.div_const 2)).add ((hq.pow 2).mul hA)
  convert hh using 1
  · funext r
    rfl
  · dsimp only [continuedUDerivative]
    norm_num
    ring

/-- Every real point on the full source cover has both strict physical derivative reserves. -/
theorem continuedU_derivative_bounds {z : ℝ} (hz : z∈Ioo (0 : ℝ) (733/1000)) :
    continuedUDerivative z<0 ∧
      (continuedUDerivative z)^2*z^2*(1-z^2)<1+(continuedU z)^2 := by
  have hzD : z∈continuationDomain := ⟨hz.1.le,hz.2.le⟩
  have hzcover : z∈Icc (((0 : ℚ) : ℝ)) (((733/1000 : ℚ) : ℝ)) := by
    norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat]
    exact ⟨hz.1.le,hz.2.le⟩
  obtain ⟨slab,hm,hs⟩:=coverCheck_sound polyak.Certificates.Continuation.P1.slabs 0 (733/1000)
    polyak.Certificates.Continuation.P1.covered hzcover
  exact allSourceSlopeCheck_sound polyak.Certificates.Continuation.P1.system
    (fun i => ((polyak.Certificates.Continuation.P1.system i).checkADSupported_eq_true_iff).mp
      (polyak.Certificates.Continuation.P1.check_supported i))
    polyak.Certificates.Continuation.P1.Slope.accepted hm hs
    (continuation_mem_box hzD hm hs) (continuation_derivative_equation hz)

/-- The actual optimal boundary has |V′|<1 everywhere in the open physical P₁ regime. -/
theorem abs_deriv_V_lt_one {z t : ℝ} (hz : z∈Ioo (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) : |deriv Spectral.V t|<1 := by
  have hzm : z∈Ioo (0 : ℝ) (733/1000) := ⟨hz.1,hz.2.trans zW_bounds.2⟩
  have hzEq : (Real.cosh t)⁻¹=z := by rw [ht]; simp
  have hparam : ContinuousAt (fun r : ℝ => (Real.cosh r)⁻¹) t :=
    (reciprocal_cosh_hasDerivAt t).continuousAt
  have hzt : (Real.cosh t)⁻¹∈Ioo (0 : ℝ) zW := by rw [hzEq]; exact hz
  have hnn : Ioo (0 : ℝ) zW∈𝓝 ((Real.cosh t)⁻¹) := Ioo_mem_nhds hzt.1 hzt.2
  have hn : ∀ᶠ r in 𝓝 t,(Real.cosh r)⁻¹∈Ioo (0 : ℝ) zW :=
    hparam.eventually hnn
  have hf : Spectral.V=ᶠ[𝓝 t] (fun r => Real.arsinh (continuedU (Real.cosh r)⁻¹)) := by
    filter_upwards [hn] with r hr
    exact continuation_optimal ⟨hr.1,hr.2.le⟩ (by simp)
  apply abs_deriv_boundary_lt_one (u:=continuedU) (du:=continuedUDerivative z) ?_ hf ?_
  · rw [hzEq]
    exact continuedU_hasDerivAt hzm
  · rw [hzEq]
    exact (continuedU_derivative_bounds hzm).2

end polyak.Boundary.P1
