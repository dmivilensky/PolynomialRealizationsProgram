import krylov.XR.FlagVariation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
Article: main_krylov, prop:status, sharp conjugate-window certificate.
Use: actual diagonal correction-base Gram matrices have orthogonal flags,
so the observed skew defect spends its budget with constant one.
Source: positive functional calculus preserves commutation and the already
proved sharp norm of an orthogonal commutator.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Secant krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
variable {p : ℕ}

/-- A genuine coordinate prefix is a contraction in Euclidean norm.
Article: main_krylov, prop:status. -/
theorem prefixProjection_norm_le_one (p l : ℕ) : ‖prefixProjection p l‖≤1 := by
  rw [prefixProjection,Matrix.l2_opNorm_diagonal,pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  split_ifs <;> norm_num

/-- Commutation with the actual Gram matrix makes its transported old
flag precisely the original orthogonal coordinate flag. Article: prop:status. -/
theorem transportedFlag_eq_of_commute (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (l : ℕ) (hcomm : Commute G (prefixProjection p l)) :
    transportedFlag G l=prefixProjection p l := by
  have hc : Commute (metricRoot G) (prefixProjection p l) := by
    simpa only [metricRoot,CFC.sqrt] using hcomm.cfcₙ_nnreal NNReal.sqrt
  rw [transportedFlag,Matrix.mul_assoc,←hc.eq,←Matrix.mul_assoc,
    nonsing_inv_mul _ (metricRoot_det_unit G hG),one_mul]

/-- Actual conjugacy makes every Gram-metric flag orthogonal.
Article: main_krylov, prop:status. -/
theorem transportedFlag_eq_of_diagonal (d : Fin p → ℝ) (hG : (diagonal d).PosDef) (l : ℕ) :
    transportedFlag (diagonal d) l=prefixProjection p l := by
  apply transportedFlag_eq_of_commute _ hG
  change diagonal d*prefixProjection p l=prefixProjection p l*diagonal d
  unfold prefixProjection
  rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- The original flag condition is exactly one for every truly conjugate
window, including its empty boundary. Article: main_krylov, prop:status. -/
theorem flagCondition_diagonal (d : Fin p → ℝ) (hG : (diagonal d).PosDef) :
    flagCondition (diagonal d)=1 := by
  apply max_eq_left
  have hh : (range p).sup (fun l=>‖transportedFlag (diagonal d) l‖₊)≤(1 : NNReal) := by
    apply Finset.sup_le
    intro l _
    rw [transportedFlag_eq_of_diagonal d hG]
    exact_mod_cast prefixProjection_norm_le_one p l
  exact_mod_cast hh

/-- On a true conjugate window, every skew flag summand spends at most
one increment budget, not twice that budget. Article: prop:status. -/
theorem conjugate_flag_commutator_bound (d : Fin p → ℝ) (hG : (diagonal d).PosDef)
    (X : Matrix (Fin p) (Fin p) ℝ) (hX : X.IsSymm) (l : ℕ) :
    relativeBudget (diagonal d) (prefixProjection p l*X-X*prefixProjection p l)≤
      relativeBudget (diagonal d) X := by
  change ‖relativeOperator (diagonal d) _‖≤‖relativeOperator (diagonal d) X‖
  rw [relative_flag_commutator _ _ hG,transportedFlag_eq_of_diagonal d hG,
    (prefixProjection_isSymm p l).eq]
  have hp : prefixProjection p l*prefixProjection p l=prefixProjection p l := by
    unfold prefixProjection
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> norm_num
  exact (matrix_commutator_norm _ _ (prefixProjection_isSymm p l) hp
    (relativeOperator_isSymm _ X hX)).2

/-- Exact observed conjugate flags give the sharp total-defect bound
under the original genuine increment budgets. Article: prop:status. -/
theorem conjugate_defect_variation (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k,(C k).IsSymm) (hG : (C p).PosDef)
    (d : Fin p → ℝ) (hdiag : C p=diagonal d) (ω : ℕ → ℝ)
    (hω : ∀ l<p,0≤ω l)
    (hbudget : ∀ l<p,relativeBudget (C p) (C (l+1)-C l)≤ω l) :
    relativeBudget (C p) (defect (observed C))≤∑ l∈range p,ω l := by
  change ‖relativeOperator (C p) (defect (observed C))‖≤_
  rw [defect_eq_sum_commutators C hC,relativeOperator_sum]
  calc
    _ ≤ ∑ l∈range (p-1),‖relativeOperator (C p)
      (prefixProjection p l*(C (l+1)-C l)-(C (l+1)-C l)*prefixProjection p l)‖ := norm_sum_le _ _
    _ ≤ ∑ l∈range (p-1),ω l := by
      apply Finset.sum_le_sum
      intro l hl
      have hp : l<p := (mem_range.mp hl).trans_le (Nat.sub_le p 1)
      have hh := conjugate_flag_commutator_bound d (hdiag ▸ hG) (C (l+1)-C l)
        ((hC _).sub (hC _)) l
      rw [←hdiag] at hh
      exact hh.trans (hbudget l hp)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le p 1))
      intro l hl _
      exact hω l (mem_range.mp hl)

/-- The original conjugate-window model error has the unamplified total
variation budget. Article: main_krylov, prop:status. -/
theorem conjugate_model_variation (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k,(C k).IsSymm) (hG : (C p).PosDef)
    (d : Fin p → ℝ) (hdiag : C p=diagonal d) (ω : ℕ → ℝ)
    (hbudget : ∀ l<p,relativeBudget (C p) (C (l+1)-C l)≤ω l) :
    relativeBudget (C p) (C p-latest (observed C))≤∑ l∈range p,ω l := by
  have hh := flag_model_variation C hC hG ω hbudget
  rw [hdiag,flagCondition_diagonal d (hdiag ▸ hG),one_pow,one_mul] at hh
  simpa only [←hdiag] using hh

/-- Full sharp retention and refutation certificates for the genuine
conjugate case of the original finite window. Article: prop:status. -/
theorem conjugate_observed_status (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k,(C k).IsSymm) (hG : (C p).PosDef)
    (d : Fin p → ℝ) (hdiag : C p=diagonal d) (ω : ℕ → ℝ)
    (hω : ∀ l<p,0≤ω l)
    (hbudget : ∀ l<p,relativeBudget (C p) (C (l+1)-C l)≤ω l)
    (θ : ℝ) (hθ : 0<θ) :
    ((∑ l∈range p,ω l)<θ/(1+θ) → windowUnrefuted θ (observed C) ∧
      relativeBudget (latest (observed C)) (C p-latest (observed C))<θ) ∧
    (¬windowUnrefuted θ (observed C) → θ/(1+θ)≤∑ l∈range p,ω l) := by
  have hm := conjugate_model_variation C hC hG d hdiag ω hbudget
  have hd := conjugate_defect_variation C hC hG d hdiag ω hω hbudget
  exact ⟨conjugate_budget_retention (C p) (observed C) hG θ _ hθ hm hd,
    conjugate_budget_refutation (C p) (observed C) hG θ _ hθ hm hd⟩

end
end krylov.XR
