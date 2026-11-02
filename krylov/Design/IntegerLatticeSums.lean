import krylov.Design.TanhLattice

/-!
Article: main_krylov, apC:lem:poisson, unconditional integer-lattice bookkeeping.
Use: real sech summability, actual product summability, and the exact even/odd
integer partition needed by the hyperbolic AGM proof.
Source: the proved positive-frequency estimates and mathlib's integer division equivalence.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young

/-- The actual real integer-lattice secant profile is absolutely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem sech_integer_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℤ => sech ((n : ℝ) * θ)) := by
  have hs := summable_even_integer (fun x : ℝ => (sech (x * θ) : ℂ))
    (fun x => by simp only [neg_mul, sech_neg])
    (Complex.summable_ofReal.mpr (sampledSech_summable hθ))
  exact Complex.summable_ofReal.mp hs

/-- Products of actual integer secant translates are genuinely summable.
Article: main_krylov, apC:lem:poisson, legitimate integer correlations. -/
theorem sech_integer_product_summable {θ : ℝ} (hθ : 0 < θ) (k : ℤ) :
    Summable (fun n : ℤ => sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ)) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (sech_pos _).le (sech_pos _).le) _
    (sech_integer_summable hθ)
  intro n
  exact mul_le_of_le_one_right (sech_pos _).le (inv_le_one_of_one_le₀ (Real.one_le_cosh _))

/-- Alternating products of genuine integer secant translates are absolutely summable.
Article: main_krylov, apC:lem:poisson, legitimate alternating correlations. -/
theorem alternating_sech_product_summable {θ : ℝ} (hθ : 0 < θ) (k : ℤ) :
    Summable (fun n : ℤ => (-1 : ℝ) ^ n * (sech ((n : ℝ) * θ) * sech (((k - n : ℤ) : ℝ) * θ))) := by
  apply (sech_integer_product_summable hθ k).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_neg_one_zpow, one_mul,
    abs_of_pos (mul_pos (sech_pos _) (sech_pos _))]

/-- A genuine summable integer series splits exactly into its even and odd lattice pairs.
Article: main_krylov, apC:lem:poisson, the hyperbolic AGM duplication proof. -/
theorem tsum_integer_even_odd (f : ℤ → ℝ) (hs : Summable f) :
    (∑' n : ℤ, f n) = ∑' n : ℤ, (f (2 * n) + f (2 * n + 1)) := by
  let e := (Int.divModEquiv 2).symm
  have hp : Summable (fun p : ℤ × Fin 2 => f (e p)) := by
    simpa only [Function.comp_def] using! hs.comp_injective e.injective
  rw [← e.tsum_eq f, hp.tsum_prod]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, Fin.sum_univ_two, e, Int.divModEquiv_symm_apply,
    Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, add_zero, mul_comm n]
  norm_num

end
end krylov.Design
