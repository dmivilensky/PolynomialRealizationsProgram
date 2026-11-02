import krylov.Secant.RelativeMetric
import Mathlib.Tactic

/-!
Article: main_krylov, thm:centre, metric slack in the admissible twin conditions.
Use: justify the change of base in all physical relative spectral budgets;
the same exact Loewner comparison handles singular or zero perturbations.
Source: reuse the proved relative-budget/Loewner equivalence and elementary
positive quadratic-form arguments. These are metric estimates, not an assumed
admissibility or an assumed expansion of the algorithm.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Secant
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A positive definite lower form makes every dominating symmetric form positive definite.
Use: the reflected base is positive as soon as its relative displacement is below one.
Article: main_krylov, thm:centre, (1−ϖ)A₀≼A₀^♯.
Proof: the difference has a nonnegative quadratic form and the lower form has
a strictly positive quadratic form on every nonzero vector. -/
theorem posDef_of_lower_form (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.IsSymm) (hAB : A ≤ B) : B.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hB)
  intro v hv
  have hp := (Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg v
  have hq := hA.dotProduct_mulVec_pos hv
  simp only [Matrix.sub_mulVec,dotProduct_sub] at hp
  linarith

/-- A strictly positive scalar multiple of an actual positive base is positive definite.
Use: the budget slack factor 1−ϖ remains a genuine positive metric.
Article: main_krylov, thm:centre, positivity under strict metric slack.
Proof: its real quadratic form is the positive scalar times the original one. -/
theorem posDef_pos_smul (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (by
      simp only [Matrix.IsSymm,transpose_smul,hA.1.isSymm.eq]))
  intro v hv
  simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul] using
    mul_pos hc (hA.dotProduct_mulVec_pos hv)

/-- A strict relative displacement yields both signed base comparisons and genuine positivity.
Use: the constructed twin base may be used as a metric after the displacement estimate.
Article: main_krylov, thm:centre, (1−ϖ)A₀≼A₀^♯≼(1+ϖ)A₀.
Proof: convert the actual displacement norm to its two physical Loewner
inequalities; its positive lower scalar form proves positive definiteness. -/
theorem relative_displacement_base (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.IsSymm) {v : ℝ} (hv : 0 ≤ v) (hv₁ : v < 1)
    (hD : relativeBudget A (B-A) ≤ v) :
    (1-v) • A ≤ B ∧ B ≤ (1+v) • A ∧ B.PosDef := by
  -- Use both signed displacement inequalities to obtain a positive lower base form.
  have hsym : (B-A).IsSymm := by
    simp only [Matrix.IsSymm,transpose_sub,hA.1.isSymm.eq,hB.eq]
  obtain ⟨hl,hu⟩ := (relative_norm_le_iff A (B-A) hA hsym hv).mp hD
  have hlow : (1-v) • A ≤ B := by
    have h := add_le_add_right hl A
    convert h using 1 <;> module
  have hupp : B ≤ (1+v) • A := by
    have h := add_le_add_right hu A
    convert h using 1 <;> module
  exact ⟨hlow,hupp,posDef_of_lower_form _ B (posDef_pos_smul A hA (by linarith)) hB hlow⟩

/-- Loewner base domination transfers an actual relative spectral budget with its exact slack.
Use: conditions H1 and H2 survive the change from the original base to the twin base.
Article: main_krylov, thm:centre, budget loss at most (1−ϖ)⁻¹.
Proof: the two signed old-metric bounds are dominated by the corresponding
new-metric endpoints, then the proved relative norm characterization applies. -/
theorem relative_budget_change (A B E : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hE : E.IsSymm)
    {c w : ℝ} (hc : 0 ≤ c) (hw : 0 ≤ w) (hAB : c • A ≤ B)
    (hbudget : relativeBudget A E ≤ c*w) : relativeBudget B E ≤ w := by
  -- Scale the base domination once and use it at both signed budget endpoints.
  obtain ⟨hl,hu⟩ := (relative_norm_le_iff A E hA hE (mul_nonneg hc hw)).mp hbudget
  apply (relative_norm_le_iff B E hB hE hw).mpr
  have hscale := smul_le_smul_of_nonneg_left hAB hw
  have he : w • (c • A)=(c*w) • A := by rw [smul_smul,mul_comm]
  rw [he] at hscale
  exact ⟨(neg_le_neg hscale).trans hl,hu.trans hscale⟩

end
end krylov.Information
