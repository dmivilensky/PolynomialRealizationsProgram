import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Article: jacobi, Lemma E.1.
The cutoff only selects the fixed real starting ray; each spatial
point farther along that ray has the exact smaller tail mass 1/x.
Use: outgoingOperator and the Jost inverse use its genuine finite L1 norm, while outgoingIntegral_ray_bound gives the sharper spatial remainder bound.
-/
namespace jacobi.Hankel
noncomputable section
open Real Set MeasureTheory

/-- The actual inverse-square coefficient restricted to a fixed positive real ray.
Use: outgoingOperator and the Jost inverse use its genuine finite L1 norm, while outgoingIntegral_ray_bound gives the sharper spatial remainder bound.
Article: jacobi, Lemma E.1.
-/
def inverseSquare (R y : ℝ) : ℝ := (Ioi R).indicator (fun x : ℝ => x^(-2:ℝ)) y

/-- The actual truncated inverse-square potential is nonnegative everywhere.
Use: its genuine ordinary integral is its L1 norm and controls the outgoing Jost contraction.
Article: jacobi, Lemma E.1.
Proof: a real power of a nonnegative positive-ray coordinate is nonnegative; outside the ray the coefficient is zero. -/
theorem inverseSquare_nonneg {R : ℝ} (hR : 0<R) (y : ℝ) : 0 ≤ inverseSquare R y := by
  apply indicator_nonneg _ y
  intro x hx
  exact Real.rpow_nonneg (hR.trans hx).le _

/-- The actual inverse-square tail is genuinely L1 on the real line for every positive cutoff.
Use: the outgoing Volterra operator and its analytic Jost inverse have all integrability premises discharged by the original inverse-square potential.
Article: jacobi, Lemma E.1.
Proof: use the community integrability theorem for the power -2 on the genuine positive ray and the measurable-indicator equivalence. -/
theorem inverseSquare_integrable {R : ℝ} (hR : 0<R) : Integrable (inverseSquare R) := by
  unfold inverseSquare
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_Ioi_rpow_of_lt (by norm_num) hR

/-- The genuine truncated inverse-square potential has exactly mass 1/R.
Use: the actual Jost integral operator has norm at most 1/R, giving a common complex-order contraction on a sufficiently far fixed ray.
Article: jacobi, Lemma E.1.
Proof: the measurable indicator converts the full integral to the real positive ray; evaluate the actual improper real-power integral using its proved exponent condition. -/
theorem inverseSquare_integral {R : ℝ} (hR : 0<R) : (∫ y : ℝ,inverseSquare R y)=1/R := by
  unfold inverseSquare
  rw [integral_indicator measurableSet_Ioi,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hR]
  norm_num [Real.rpow_neg_one]

/-- The actual inverse-square tail has precisely L1 norm 1/R.
Use: outgoingOperator_norm_le and the Jost inverse bounds are exact consequences of the original source potential, with no numerical tail certificate.
Article: jacobi, Lemma E.1.
Proof: the potential is genuinely nonnegative, so its norm integrand equals itself; use its independently evaluated actual integral. -/
theorem inverseSquare_norm_integral {R : ℝ} (hR : 0<R) :
    (∫ y : ℝ,‖inverseSquare R y‖)=1/R := by
  simp_rw [Real.norm_eq_abs,abs_of_nonneg (inverseSquare_nonneg hR _)]
  exact inverseSquare_integral hR

end
end jacobi.Hankel
