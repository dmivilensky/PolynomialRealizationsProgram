import krylov.Design.HyperbolicProducts
import krylov.Design.PoissonSech

/-!
Article: main_krylov, apC:lem:poisson, the complementary-period nome bridge.
Use: prove genuine half-lattice Poisson summation for sech, including actual
convergence and positivity. This identifies the true alternating mass with
the true complementary half-lattice mass, without an assumed theta formula.
Source: the independently proved exact transform and mathlib Poisson summation.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young
open scoped Topology FourierTransform

/-- The genuine positive secant mass on the half-shifted integer lattice.
Article: main_krylov, apC:lem:poisson, the complementary elliptic period. -/
def latticeSechHalfMass (θ : ℝ) : ℝ := ∑' n : ℤ, sech (((n : ℝ) + 1 / 2) * θ)

/-- The true positive half-lattice samples are summable.
Article: main_krylov, apC:lem:poisson. -/
theorem sech_half_nat_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => sech (((n : ℝ) + 1 / 2) * θ)) := by
  have hs : Summable (fun n : ℕ => sech ((n : ℝ) * θ)) := by
    simpa only [Int.cast_natCast] using! (sech_integer_summable hθ).comp_injective (show Function.Injective (fun n : ℕ => (n : ℤ)) from Nat.cast_injective)
  apply Summable.of_nonneg_of_le (fun n => (sech_pos _).le) _ hs
  intro n
  exact sech_antitoneOn (mul_nonneg (Nat.cast_nonneg _) hθ.le)
    (show 0 ≤ ((n : ℝ) + 1 / 2) * θ by positivity) (by nlinarith)

/-- The genuine half-shifted integer secant mass is absolutely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem sech_half_integer_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℤ => sech (((n : ℝ) + 1 / 2) * θ)) := by
  have hp : Summable (fun n : ℕ => sech ((((n : ℤ) : ℝ) + 1 / 2) * θ)) := by
    simpa only [Int.cast_natCast] using sech_half_nat_summable hθ
  have hn : Summable (fun n : ℕ => sech (((-((n : ℤ) + 1) : ℤ) + 1 / 2 : ℝ) * θ)) := by
    convert! sech_half_nat_summable hθ using 1
    funext n
    rw [show ((-((n : ℤ) + 1) : ℤ) + 1 / 2 : ℝ) * θ = -(((n : ℝ) + 1 / 2) * θ) by
      push_cast
      ring, sech_neg]
  exact Summable.of_nat_of_neg_add_one
    (f := fun n : ℤ => sech (((n : ℝ) + 1 / 2) * θ)) hp hn

/-- The actual half-lattice mass is strictly positive.
Article: main_krylov, apC:lem:poisson. -/
theorem latticeSechHalfMass_pos {θ : ℝ} (hθ : 0 < θ) : 0 < latticeSechHalfMass θ :=
  (sech_half_integer_summable hθ).tsum_pos (fun _ => (sech_pos _).le) 0 (sech_pos _)

/-- The exact Fourier character at the half-period is the genuine integer alternating sign.
Article: main_krylov, apC:lem:poisson. -/
theorem fourier_half_integer (n : ℤ) :
    fourier n ((1 / 2 : ℝ) : UnitAddCircle) = (-1 : ℂ) ^ n := by
  rw [fourier_coe_apply]
  rw [show (2 : ℂ) * π * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ) / ((1 : ℝ) : ℂ) =
    (n : ℂ) * ((π : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- The genuine half-lattice Poisson identity identifies the complementary alternating sech mass.
Article: main_krylov, apC:lem:poisson, the elliptic nome reformulation. -/
theorem poisson_sech_half {θ : ℝ} (hθ : 0 < θ) :
    latticeSechHalfMass θ = π / θ * latticeSechAlternatingMass (π ^ 2 / θ) := by
  let f : ℝ → ℂ := fun x => (sech (θ * x) : ℂ)
  have hc : Continuous f := Complex.continuous_ofReal.comp
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
      (fun x => (Real.cosh_pos (θ * x)).ne'))
  have hsF := summable_even_integer (𝓕 f) (fourier_scaled_sech_even hθ)
    (fourier_scaled_sech_summable_positive hθ)
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc
    (by norm_num : (1 : ℝ) < 2) (scaled_sech_isBigO_inv_square hθ) hsF (1 / 2)
  have hl : (∑' n : ℤ, f (1 / 2 + (n : ℝ))) = (latticeSechHalfMass θ : ℂ) := by
    rw [latticeSechHalfMass, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    dsimp [f]
    rw [show θ * (1 / 2 + (n : ℝ)) = ((n : ℝ) + 1 / 2) * θ by ring]
  have hr : (∑' n : ℤ, 𝓕 f n * fourier n ((1 / 2 : ℝ) : UnitAddCircle)) =
      ((π / θ : ℝ) : ℂ) * (latticeSechAlternatingMass (π ^ 2 / θ) : ℂ) := by
    rw [latticeSechAlternatingMass, Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [fourier_scaled_sech hθ, fourier_half_integer]
    rw [show π ^ 2 * (n : ℝ) / θ = (n : ℝ) * (π ^ 2 / θ) by ring]
    push_cast
    ring
  rw [hl, hr] at hp
  exact_mod_cast hp

/-- The genuine alternating integer secant mass is strictly positive at every positive spacing.
Article: main_krylov, apC:lem:poisson, positivity of the elliptic complementary parameter.
Proof: actual half-lattice Poisson summation at the reciprocal spacing. -/
theorem latticeSechAlternatingMass_pos {θ : ℝ} (hθ : 0 < θ) : 0 < latticeSechAlternatingMass θ := by
  have hA : 0 < π ^ 2 / θ := div_pos (sq_pos_of_pos Real.pi_pos) hθ
  have hp := poisson_sech_half hA
  have hi : π ^ 2 / (π ^ 2 / θ) = θ := by field_simp
  rw [hi] at hp
  have hc := latticeSechHalfMass_pos hA
  rw [hp] at hc
  exact (mul_pos_iff_of_pos_left (div_pos Real.pi_pos hA)).mp hc

end
end krylov.Design
