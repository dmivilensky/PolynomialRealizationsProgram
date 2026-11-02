import krylov.Stability.CanonicalResponseCoordinates

/-!
Article: main_krylov, apB:lem:UArem, true finite oblique response bounds.
Use: turn actual uniform step and weighted flag estimates into a genuine
quadratic full-cycle response error without minimum-energy denominators.
Source: actual finite tail summation, operator norm products, the true
spectral transpose isometry and proved normalized oblique flag norm bound.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The difference of actual finite displacement tails is bounded by horizon times the true individual step error.
Use: The difference of actual finite displacement tails is bounded by horizon times the true individual step error.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Sum the real step differences and bound the actual tail cardinality by the horizon. -/
theorem finite_tail_difference (s t : ℕ → EuclideanSpace ℝ (Fin n)) (N l : ℕ) {ε : ℝ}
    (hε : 0≤ε) (he : ∀ j<N, ‖s j-t j‖≤ε) :
    ‖(∑ j∈Ico (l+1) N, s j)-(∑ j∈Ico (l+1) N, t j)‖≤(N : ℝ)*ε := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j∈Ico (l+1) N, ‖s j-t j‖ := norm_sum_le _ _
    _ ≤ ∑ _j∈Ico (l+1) N, ε := sum_le_sum fun j hj => he j (mem_Ico.mp hj).2
    _ ≤ (N : ℝ)*ε := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show (Ico (l+1) N).card≤N by simp only [Nat.card_Ico];omega)) hε

/-- A genuine operator response difference is controlled by the actual tail error and its weighted flag change.
Use: A genuine operator response difference is controlled by the actual tail error and its weighted flag change.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Split into the real changed input and changed operator terms; retain the true input norm paired with its own flag error. -/
theorem operator_response_difference (P Q F : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (a b : EuclideanSpace ℝ (Fin n)) {ε η : ℝ} (hP : ‖P‖≤2)
    (he : ‖a-b‖≤ε) (hq : ‖b‖*‖P-Q‖≤η) :
    ‖P (F a)-Q (F b)‖≤‖F‖*(2*ε+η) := by
  -- Preserve the reference input weight in the operator-change term.
  have hsplit : P (F a)-Q (F b)=P (F (a-b))+(P-Q) (F b) := by simp only [map_sub,_root_.sub_apply]; abel
  have h₁ : ‖P (F (a-b))‖≤2*(‖F‖*ε) :=
    (P.le_opNorm _).trans (mul_le_mul hP ((F.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left he (norm_nonneg _))) (norm_nonneg _) (by norm_num))
  have h₂ : ‖(P-Q) (F b)‖≤‖F‖*η := by
    calc
      _ ≤ ‖P-Q‖*(‖F‖*‖b‖) := (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (F.le_opNorm _) (norm_nonneg _))
      _ = ‖F‖*(‖b‖*‖P-Q‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
  rw [hsplit]
  exact (norm_add_le _ _).trans (by nlinarith)

/-- The actual finite oblique responses obey the genuine total-budget times step-and-weighted-flag error bound.
Use: The actual finite oblique responses obey the genuine total-budget times step-and-weighted-flag error bound.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Apply the proved two-term operator inequality to each actual transposed flag, using its true norm at most two and the real finite tail bound, and sum with the actual spectral increment norms. -/
theorem obliqueResponse_difference_bound (T Q : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (s t : ℕ → EuclideanSpace ℝ (Fin n))
    {ε η : ℝ} (hε : 0≤ε) (hG : ‖Tᵀ*T-1‖≤1/2)
    (he : ∀ j<n, ‖s j-t j‖≤ε)
    (hflag : ∀ l<n, ‖∑ j∈Ico (l+1) n, t j‖*‖transportedFlag T l-transportedFlag Q l‖≤η) :
    ‖obliqueResponse T E s-obliqueResponse Q E t‖≤(∑ l∈range n, ‖E l‖)*(2*(n : ℝ)*ε+η) := by
  -- The actual transpose is an isometry, so the proved weighted matrix flags apply directly.
  unfold obliqueResponse
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ l∈range n, ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag T l)ᵀ)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (∑ j∈Ico (l+1) n, s j))-
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag Q l)ᵀ)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (∑ j∈Ico (l+1) n, t j))‖ := norm_sum_le _ _
    _ ≤ ∑ l∈range n, ‖E l‖*(2*((n : ℝ)*ε)+η) := by
      apply sum_le_sum
      intro l hl
      have hn := transportedFlag_norm_two T hG l
      have ht : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag T l)ᵀ‖≤2 := by
        rw [Matrix.l2_opNorm_toEuclideanCLM,transpose_norm]; exact hn
      have hf : ‖∑ j∈Ico (l+1) n, t j‖*
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag T l)ᵀ-
            Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag Q l)ᵀ‖≤η := by
        rw [← map_sub,← Matrix.transpose_sub,Matrix.l2_opNorm_toEuclideanCLM,transpose_norm]
        exact hflag l (mem_range.mp hl)
      have h := operator_response_difference _ _ (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l)) _ _ ht
        (finite_tail_difference s t n l hε he) hf
      rw [Matrix.l2_opNorm_toEuclideanCLM] at h
      exact h
    _ = _ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro l _
      ring
end
end krylov.Stability
