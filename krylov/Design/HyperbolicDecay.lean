import krylov.Design.HyperbolicFourier
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
Article: main_krylov, apC:lem:poisson, genuine Poisson regularity hypotheses.
Use: verify actual quadratic decay of the rescaled hyperbolic profiles by an
elementary global cosh bound. This supplies mathlib's Poisson summation input
without an assumed Schwartz-space structure or assumed decay estimate.
Source: cosh's double-angle identity and sinh(x)>=x for x>=0.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young Asymptotics Set
open scoped Topology FourierTransform

/-- The actual hyperbolic cosine dominates its quadratic Taylor lower bound globally.
Article: main_krylov, apC:lem:poisson.
Proof: use the double-angle identity and the genuine monotonicity bound sinh(t)>=t. -/
theorem cosh_quadratic_lower (x : ℝ) : 1 + x ^ 2 / 2 ≤ cosh x := by
  wlog hx : 0 ≤ x generalizing x
  · have h := this (-x) (by linarith)
    simpa only [Real.cosh_neg, neg_sq] using h
  have hs := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ x / 2)
  have hd := Real.cosh_two_mul (x / 2)
  rw [show (2 : ℝ) * (x / 2) = x by ring] at hd
  have hc := Real.cosh_sq_sub_sinh_sq (x / 2)
  nlinarith [sq_nonneg (sinh (x / 2) - x / 2)]

/-- Every scaled actual secant sample obeys a concrete inverse-square bound away from zero.
Article: main_krylov, apC:lem:poisson. -/
theorem sech_scaled_inv_square_bound {θ : ℝ} (hθ : 0 < θ) {x : ℝ} (hx : x ≠ 0) :
    sech (θ * x) ≤ (2 / θ ^ 2) * (x ^ 2)⁻¹ := by
  have hp : 0 < (θ * x) ^ 2 / 2 := by positivity
  have hb : (θ * x) ^ 2 / 2 ≤ cosh (θ * x) := by
    have h := cosh_quadratic_lower (θ * x)
    linarith
  unfold jacobi.Young.sech
  rw [← one_div (cosh (θ * x))]
  calc
    1 / cosh (θ * x) ≤ 1 / ((θ * x) ^ 2 / 2) := one_div_le_one_div_of_le hp hb
    _ = (2 / θ ^ 2) * (x ^ 2)⁻¹ := by field_simp

/-- The actual scaled secant meets mathlib's quadratic cocompact decay hypothesis.
Article: main_krylov, apC:lem:poisson. -/
theorem scaled_sech_isBigO_inv_square {θ : ℝ} (hθ : 0 < θ) :
    (fun x : ℝ => (sech (θ * x) : ℂ)) =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (2 / θ ^ 2)
  have hevent : ∀ᶠ x : ℝ in cocompact ℝ, x ≠ 0 :=
    (isCompact_singleton : IsCompact ({0} : Set ℝ)).compl_mem_cocompact
  filter_upwards [hevent] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sech_pos _), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _),
    Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
  exact sech_scaled_inv_square_bound hθ hx

/-- The actual scaled squared secant meets the same quadratic cocompact decay hypothesis.
Article: main_krylov, apC:lem:poisson. -/
theorem scaled_sechSquared_isBigO_inv_square {θ : ℝ} (hθ : 0 < θ) :
    (fun x : ℝ => (sech (θ * x) : ℂ) ^ 2) =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  have hnorm (x : ℝ) : ‖(sech (θ * x) : ℂ) ^ 2‖ ≤ ‖(sech (θ * x) : ℂ)‖ := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sech_pos _)]
    have hle : sech (θ * x) ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh _)
    nlinarith [sech_pos (θ * x)]
  exact (Asymptotics.IsBigO.of_norm_le (fun x => hnorm x)).trans
    ((scaled_sech_isBigO_inv_square hθ).norm_left)

end
end krylov.Design
