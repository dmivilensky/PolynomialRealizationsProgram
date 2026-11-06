import chebyshev1.Perturbations.SmoothExpansion
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Uniform Peano expansion from differentiability of the derivative at one
point. No continuity of the second derivative on a neighborhood is assumed. -/
namespace chebyshev1.Perturbations
noncomputable section
open Filter Set Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiability near zero and differentiability of the derivative at zero
are the pointwise second differentiability hypotheses. -/
theorem pointwise_second_order_taylor (g : E → F)
    (hg : ∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ g x)
    (h2 : DifferentiableAt ℝ (fderiv ℝ g) 0) :
    (fun x => g x-g 0-fderiv ℝ g 0 x-
      (1/2:ℝ) • (fderiv ℝ (fderiv ℝ g) 0 x) x)
      =o[𝓝 0] (fun x : E => ‖x‖^2) := by
  let A := fderiv ℝ g 0
  let B := fderiv ℝ (fderiv ℝ g) 0
  let R := fun x => g x-g 0-A x-(1/2:ℝ) • (B x) x
  let D := fun x => fderiv ℝ g x-A-B x
  have hgf : ∀ᶠ x in 𝓝 (0:E), HasFDerivAt g (fderiv ℝ g x) x :=
    hg.mono (fun _ hx => hx.hasFDerivAt)
  have hsym (x y : E) : (B x) y = (B y) x :=
    second_derivative_symmetric_of_eventually_of_real hgf h2.hasFDerivAt x y
  have hflip (x : E) : B.flip x = B x := by
    ext y
    exact hsym y x
  have hquad (x : E) : HasFDerivAt (fun x => (1/2:ℝ) • (B x) x) (B x) x := by
    have hh := (B.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_smul (1/2:ℝ)
    rw [ContinuousLinearMap.comp_id, hflip] at hh
    convert hh using 1
    · rfl
    · ext y
      change (B x) y = (1/2:ℝ) • ((B x) y+(B x) y)
      module
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgf
  let s := Metric.ball (0:E) r
  have hs0 : (0:E) ∈ s := Metric.mem_ball_self hr
  have hder (x : E) (hx : x ∈ s) : HasFDerivWithinAt R (D x) s x := by
    exact (((hball hx).sub_const (g 0)).sub A.hasFDerivAt |>.sub (hquad x)).hasFDerivWithinAt
  have hD : D =o[𝓝 (0:E)] (fun x => ‖x‖) := by
    simpa only [D, A, B, sub_zero] using h2.hasFDerivAt.isLittleO.norm_right
  have hh := (convex_ball (0:E) r).isLittleO_pow_succ (n := 1) hs0 hder
    (by simpa only [sub_zero, pow_one] using hD.mono nhdsWithin_le_nhds)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0:E) hr)] at hh
  simpa only [R, A, B, sub_self, map_zero, zero_apply, smul_zero, sub_zero] using hh

end
end chebyshev1.Perturbations
