import krylov.LotkaVolterra.AnalyticSaddleLift
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Article: main_krylov, apC:prop:LV, analytic saddle construction.
Use: verify the crucial zero derivative in the unknown path for the actual
nonlinear chord equation. Evaluation along every affine path reduces this to
the concrete scalar derivative of H; no derivative certificate is assumed.
Source: uniqueness of Fréchet/directional derivatives and algebra inversion.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Filter
open krylov.AnalyticTools
open scoped Topology

theorem saddleLift_units_eventually {γ c r : ℝ} (hγ : γ < 1) (hr : r < 1) :
    ∀ᶠ p : ℝ × SaddlePaths in 𝓝 (0, 0),
      IsUnit (ContinuousMap.const SymmetricPathDomain (saddleU γ) - saddleLiftZ c p) ∧
      IsUnit (1 - saddleLiftV r p) := by
  have hu := saddleLift_units_zero (c := c) hγ hr
  have hA : Continuous (fun p : ℝ × SaddlePaths ↦
      ContinuousMap.const SymmetricPathDomain (saddleU γ) - saddleLiftZ c p) := by
    unfold saddleLiftZ
    fun_prop
  have hB : Continuous (fun p : ℝ × SaddlePaths ↦ 1 - saddleLiftV r p) := by
    unfold saddleLiftV
    fun_prop
  have heA : ∀ᶠ p : ℝ × SaddlePaths in 𝓝 (0, 0),
      IsUnit (ContinuousMap.const SymmetricPathDomain (saddleU γ) - saddleLiftZ c p) :=
    hA.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hu.1)
  have heB : ∀ᶠ p : ℝ × SaddlePaths in 𝓝 (0, 0), IsUnit (1 - saddleLiftV r p) :=
    hB.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hu.2)
  exact heA.and heB

/-- After moving -a*w to the singular operator, the true derivative in w is
zero on the entire continuous-path Banach space. -/
theorem saddleNonlinearLift_hasFDerivAt {γ c r : ℝ} (hγ : γ < 1) (hr : r < 1) :
    ∃ A : ℝ →L[ℝ] SaddlePaths, HasFDerivAt
      (saddleNonlinearLift γ c r (-saddleSlopeDerivative γ 0 r)) (A.coprod 0) (0, 0) := by
  let N := saddleNonlinearLift γ c r (-saddleSlopeDerivative γ 0 r)
  let D := fderiv ℝ N (0, 0)
  have hd : HasFDerivAt N D (0, 0) :=
    (analyticAt_saddleNonlinearLift hγ hr).differentiableAt.hasFDerivAt
  have hzero (w : SaddlePaths) : D (0, w) = 0 := by
    ext u
    let line : ℝ → ℝ × SaddlePaths := fun t ↦ (0, t • w)
    have hl : HasDerivAt line (0, w) 0 := by
      convert (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk
        ((hasDerivAt_id (0 : ℝ)).smul_const w) using 1 <;>
        first | rfl | simp only [one_smul]
    let ev : SaddlePaths →L[ℝ] ℝ := ContinuousMap.evalCLM (R := ℝ) u
    have hd₀ : HasFDerivAt N D (line 0) := by simpa [line] using hd
    have hdcurve : HasDerivAt (fun t ↦ N (line t) u) (D (0, w) u) 0 := by
      exact ev.hasFDerivAt.comp_hasDerivAt 0 (hd₀.comp_hasDerivAt 0 hl)
    have ht : Tendsto line (𝓝 0) (𝓝 ((0 : ℝ), (0 : SaddlePaths))) := by
      have hh := hl.continuousAt
      change Tendsto line (𝓝 0) (𝓝 (line 0)) at hh
      simpa only [line, zero_smul] using hh
    have heq : (fun t ↦ N (line t) u) =ᶠ[𝓝 0] (fun t : ℝ ↦
        saddleSlopeRate γ 0 (r + t * w u) - saddleSlopeDerivative γ 0 r * (t * w u)) := by
      filter_upwards [ht.eventually (saddleLift_units_eventually (c := c) hγ hr)] with t ht
      simpa [N, line, neg_mul, sub_eq_add_neg] using
        saddleNonlinearLift_apply (a := -saddleSlopeDerivative γ 0 r) ht.1 ht.2 u
    have hrr : HasDerivAt (fun t : ℝ ↦ r + t * w u) (w u) 0 := by
      convert! ((hasDerivAt_id (0 : ℝ)).mul_const (w u)).const_add r using 1
      simp only [one_mul]
    have hscalar : HasDerivAt (fun t : ℝ ↦
        saddleSlopeRate γ 0 (r + t * w u) - saddleSlopeDerivative γ 0 r * (t * w u)) 0 0 := by
      have h := ((saddleSlopeRate_hasDerivAt (γ := γ) (z := 0)
        (v := r) (by linarith : 1 - r ≠ 0)).comp_of_eq 0 hrr (by simp)).sub
        (((hasDerivAt_id (0 : ℝ)).mul_const (w u)).const_mul (saddleSlopeDerivative γ 0 r))
      convert h using 1 <;> first | rfl | ring
    exact hdcurve.unique (hscalar.congr_of_eventuallyEq heq)
  let A : ℝ →L[ℝ] SaddlePaths := D.comp (ContinuousLinearMap.inl ℝ ℝ SaddlePaths)
  have heq : D = A.coprod 0 := by
    apply ContinuousLinearMap.ext
    intro p
    have h := D.map_add (p.1, 0) (0, p.2)
    simpa [A, ContinuousLinearMap.coprod_apply, hzero] using h
  exact ⟨A, heq ▸ hd⟩

end
end krylov.LotkaVolterra
