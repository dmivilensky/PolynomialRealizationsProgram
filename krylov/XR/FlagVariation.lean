import krylov.XR.VariationThreshold

/-!
Article: main_krylov, prop:status, actual finite variation certificates.
Use: sum the exact chronological flag identities under the original
increment budgets; no model-accuracy or test-success certificate is an
execution input. Source: proved old-flag decomposition and metric transfer.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Secant
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
variable {p n : ℕ}

/-- Actual positive-root normalization commutes with finite sums.
Article: main_krylov, prop:status. -/
theorem relativeOperator_sum {ι : Type*} (G : Matrix (Fin p) (Fin p) ℝ)
    (s : Finset ι) (X : ι → Matrix (Fin p) (Fin p) ℝ) :
    relativeOperator G (∑ l∈s,X l)=∑ l∈s,relativeOperator G (X l) := by
  simp only [relativeOperator,Matrix.mul_sum,Matrix.sum_mul]

/-- The original observed model error spends at most kappa_flat squared
times the actual total variation allowance. Article: prop:status. -/
theorem flag_model_variation (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k,(C k).IsSymm) (hG : (C p).PosDef) (ω : ℕ → ℝ)
    (hbudget : ∀ l<p,relativeBudget (C p) (C (l+1)-C l)≤ω l) :
    relativeBudget (C p) (C p-latest (observed C))≤flagCondition (C p)^2*(∑ l∈range p,ω l) := by
  change ‖relativeOperator (C p) (C p-latest (observed C))‖≤_
  rw [model_error_eq_sum_compressions C hC,relativeOperator_sum]
  calc
    _ ≤ ∑ l∈range p,‖relativeOperator (C p)
      (prefixProjection p l*(C (l+1)-C l)*prefixProjection p l)‖ := norm_sum_le _ _
    _ ≤ ∑ l∈range p,flagCondition (C p)^2*ω l := by
      apply Finset.sum_le_sum
      intro l hl
      exact relative_flag_compression_bound _ _ hG l (mem_range.mp hl) (ω l) (hbudget l (mem_range.mp hl))
    _ = _ := by rw [Finset.mul_sum]

/-- The actual observed defect obeys the original general-window
variation bound. The last increment is correctly absent from its exact
flag identity. Article: main_krylov, prop:status. -/
theorem flag_defect_variation (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k,(C k).IsSymm) (hG : (C p).PosDef) (ω : ℕ → ℝ)
    (hω : ∀ l<p,0≤ω l)
    (hbudget : ∀ l<p,relativeBudget (C p) (C (l+1)-C l)≤ω l) :
    relativeBudget (C p) (defect (observed C))≤2*flagCondition (C p)^2*(∑ l∈range p,ω l) := by
  change ‖relativeOperator (C p) (defect (observed C))‖≤_
  rw [defect_eq_sum_commutators C hC,relativeOperator_sum]
  have hs : ∑ l∈range (p-1),ω l≤∑ l∈range p,ω l := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le p 1))
    intro l hl _
    exact hω l (mem_range.mp hl)
  calc
    _ ≤ ∑ l∈range (p-1),‖relativeOperator (C p)
      (prefixProjection p l*(C (l+1)-C l)-(C (l+1)-C l)*prefixProjection p l)‖ := norm_sum_le _ _
    _ ≤ ∑ l∈range (p-1),2*flagCondition (C p)^2*ω l := by
      apply Finset.sum_le_sum
      intro l hl
      have hp : l<p := (mem_range.mp hl).trans_le (Nat.sub_le p 1)
      exact relative_flag_commutator_bound _ _ hG l hp (ω l) (hbudget l hp)
    _ = 2*flagCondition (C p)^2*(∑ l∈range (p-1),ω l) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Refutation of a genuinely generated finite window certifies the
printed total-variation lower bound with its actual flag condition.
Article: main_krylov, prop:status. -/
theorem observed_variation_refutation (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k,(C k).IsSymm) (hG : (C p).PosDef) (ω : ℕ → ℝ)
    (hω : ∀ l<p,0≤ω l)
    (hbudget : ∀ l<p,relativeBudget (C p) (C (l+1)-C l)≤ω l)
    (θ : ℝ) (hθ : 0<θ) (hrefute : ¬windowUnrefuted θ (observed C)) :
    θ/((2+θ)*flagCondition (C p)^2)≤∑ l∈range p,ω l := by
  exact variation_budget_refutation (C p) (observed C) hG θ (flagCondition (C p))
    (∑ l∈range p,ω l) hθ (one_le_flagCondition _)
    (flag_model_variation C hC hG ω hbudget) (flag_defect_variation C hC hG ω hω hbudget) hrefute

/-- Below the original threshold, a genuinely generated window passes
its actual Hermitian test and has the printed model-error radius.
Article: main_krylov, prop:status. -/
theorem observed_variation_retention (C : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ k,(C k).IsSymm) (hG : (C p).PosDef) (ω : ℕ → ℝ)
    (hω : ∀ l<p,0≤ω l)
    (hbudget : ∀ l<p,relativeBudget (C p) (C (l+1)-C l)≤ω l)
    (θ : ℝ) (hθ : 0<θ)
    (hsmall : (∑ l∈range p,ω l)<θ/((2+θ)*flagCondition (C p)^2)) :
    windowUnrefuted θ (observed C) ∧
      relativeBudget (latest (observed C)) (C p-latest (observed C))<θ/2 := by
  exact variation_budget_retention (C p) (observed C) hG θ (flagCondition (C p))
    (∑ l∈range p,ω l) hθ (one_le_flagCondition _)
    (flag_model_variation C hC hG ω hbudget) (flag_defect_variation C hC hG ω hω hbudget) hsmall

end
end krylov.XR
