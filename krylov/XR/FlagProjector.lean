import krylov.XR.MetricTransfer
import krylov.LinearAlgebra.Commutator

/-!
Article: main_krylov, prop:status, actual transported flag projectors.
Use: quantify the window's observed conditioning in its correction-base
Gram metric and normalize the exact flag identities without approximation.
Source: genuine positive-root algebra and finite operator-norm bounds.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Secant
open scoped Matrix.Norms.L2Operator BigOperators
variable {p : ℕ}

/-- The true old-flag projector in the correction-base Gram metric.
Article: main_krylov, prop:status, Pi_l. -/
def transportedFlag (G : Matrix (Fin p) (Fin p) ℝ) (l : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  (metricRoot G)⁻¹*prefixProjection p l*metricRoot G

/-- Exactly the maximum of one and all actual transported flag norms.
Article: main_krylov, prop:status, kappa_flat. -/
def flagCondition (G : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  max 1 (((range p).sup (fun l=>‖transportedFlag G l‖₊) : NNReal) : ℝ)

/-- The actual flag condition is at least one, also for the empty window.
Article: main_krylov, prop:status. -/
theorem one_le_flagCondition (G : Matrix (Fin p) (Fin p) ℝ) : 1≤flagCondition G := le_max_left _ _

/-- Every actually used old flag is bounded by the original common
condition number. Article: main_krylov, prop:status. -/
theorem transportedFlag_norm_le (G : Matrix (Fin p) (Fin p) ℝ) (l : ℕ) (hl : l<p) :
    ‖transportedFlag G l‖≤flagCondition G := by
  have hh : ‖transportedFlag G l‖≤
      (((range p).sup (fun j=>‖transportedFlag G j‖₊) : NNReal) : ℝ) := by
    exact_mod_cast (Finset.le_sup (f := fun j=>‖transportedFlag G j‖₊) (mem_range.mpr hl))
  exact hh.trans (le_max_right _ _)

/-- Transported flags are actual idempotents. Article: prop:status. -/
theorem transportedFlag_idempotent (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) (l : ℕ) :
    transportedFlag G l*transportedFlag G l=transportedFlag G l := by
  have hp : prefixProjection p l*prefixProjection p l=prefixProjection p l := by
    unfold prefixProjection
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> norm_num
  simp only [transportedFlag,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (metricRoot G) (metricRoot G)⁻¹,
    mul_nonsing_inv _ (metricRoot_det_unit G hG),one_mul,
    ←Matrix.mul_assoc (prefixProjection p l) (prefixProjection p l) (metricRoot G),hp]

/-- Normalizing an old symmetric compression is exactly congruence by
the transported flag. Article: main_krylov, prop:status. -/
theorem relative_flag_compression (G X : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) (l : ℕ) :
    relativeOperator G (prefixProjection p l*X*prefixProjection p l)=
      transportedFlag G l*relativeOperator G X*(transportedFlag G l)ᵀ := by
  calc
    _ = relativeOperator G (prefixProjection p l*
      (metricRoot G*relativeOperator G X*metricRoot G)*prefixProjection p l) := by
      rw [relativeOperator_reconstruct G X hG]
    _ = _ := by
      simp only [transportedFlag,relativeOperator,transpose_mul,transpose_nonsing_inv,
        (metricRoot_isSymm G).eq,(prefixProjection_isSymm p l).eq,Matrix.mul_assoc]

/-- Normalizing a genuine observed flag commutator is exactly the
transported skew cross form. Article: main_krylov, prop:status. -/
theorem relative_flag_commutator (G X : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) (l : ℕ) :
    relativeOperator G (prefixProjection p l*X-X*prefixProjection p l)=
      transportedFlag G l*relativeOperator G X-relativeOperator G X*(transportedFlag G l)ᵀ := by
  simp only [transportedFlag,transpose_mul,transpose_nonsing_inv,
    (metricRoot_isSymm G).eq,(prefixProjection_isSymm p l).eq,relativeOperator,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (metricRoot G) (metricRoot G)⁻¹,
    mul_nonsing_inv _ (metricRoot_det_unit G hG),one_mul,
    ←Matrix.mul_assoc (metricRoot G)⁻¹ (metricRoot G),
    nonsing_inv_mul _ (metricRoot_det_unit G hG),one_mul]

/-- The exact model-error summand spends at most the square of the
actual flag condition times its increment budget. Article: prop:status. -/
theorem relative_flag_compression_bound (G X : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (l : ℕ) (hl : l<p) (ω : ℝ) (hω : relativeBudget G X≤ω) :
    relativeBudget G (prefixProjection p l*X*prefixProjection p l)≤flagCondition G^2*ω := by
  change ‖relativeOperator G _‖≤_
  rw [relative_flag_compression G X hG]
  have ht : ‖(transportedFlag G l)ᵀ‖=‖transportedFlag G l‖ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose (transportedFlag G l)
  have hκ : 0≤flagCondition G := (by norm_num : (0:ℝ)≤1).trans (one_le_flagCondition G)
  calc
    _ ≤ ‖transportedFlag G l‖*‖relativeOperator G X‖*‖(transportedFlag G l)ᵀ‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ flagCondition G*ω*flagCondition G := by
      rw [ht]
      exact mul_le_mul (mul_le_mul (transportedFlag_norm_le G l hl) hω (norm_nonneg _) hκ)
        (transportedFlag_norm_le G l hl) (norm_nonneg _) (mul_nonneg hκ ((norm_nonneg _).trans hω))
    _ = _ := by ring

/-- Every genuine skew flag summand obeys the printed general-window
budget bound. Article: main_krylov, prop:status. -/
theorem relative_flag_commutator_bound (G X : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (l : ℕ) (hl : l<p) (ω : ℝ) (hω : relativeBudget G X≤ω) :
    relativeBudget G (prefixProjection p l*X-X*prefixProjection p l)≤2*flagCondition G^2*ω := by
  change ‖relativeOperator G _‖≤_
  rw [relative_flag_commutator G X hG]
  have ht : ‖(transportedFlag G l)ᵀ‖=‖transportedFlag G l‖ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose (transportedFlag G l)
  have hκ := one_le_flagCondition G
  have hω' : 0≤ω := (norm_nonneg _).trans hω
  have hp := transportedFlag_norm_le G l hl
  have hn : ‖transportedFlag G l*relativeOperator G X-
      relativeOperator G X*(transportedFlag G l)ᵀ‖≤
      ‖transportedFlag G l‖*‖relativeOperator G X‖+
      ‖relativeOperator G X‖*‖(transportedFlag G l)ᵀ‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  rw [ht] at hn
  have ha := mul_le_mul hp hω (norm_nonneg _) (by linarith : 0≤flagCondition G)
  have hb := mul_le_mul hω hp (norm_nonneg _) hω'
  change ‖transportedFlag G l‖*‖relativeOperator G X‖≤flagCondition G*ω at ha
  change ‖relativeOperator G X‖*‖transportedFlag G l‖≤ω*flagCondition G at hb
  have hc : flagCondition G*ω≤flagCondition G^2*ω := by
    nlinarith [mul_nonneg (by linarith : 0≤flagCondition G-1) hω',
      mul_nonneg (by nlinarith : 0≤flagCondition G^2-flagCondition G) hω']
  nlinarith

end
end krylov.XR
