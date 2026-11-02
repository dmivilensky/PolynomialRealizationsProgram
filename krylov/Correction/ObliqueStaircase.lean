import krylov.Stability.UniformFlagBounds

/-!
Article: main_krylov, thm:UCq, quantitative genuine terminal response geometry.
Use: Reuse the actual full-basis, oblique flag and measured-model algebra
in the uniform second-order RFC expansion without a smallest CG energy.
Source: proved genuine Gram conditioning, exact finite correction identities
and the existing weighted oblique response comparison.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine canonical curvature staircase of an arbitrary full column basis and its actual old transported flags.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
-/
def obliqueStaircase (T : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  F+∑ l ∈ range N, (transportedFlag T l)ᵀ*E l*transportedFlag T l

/-- The true oblique staircase has four-times-total-increment plus actual terminal-defect norm control under genuine half-Gram conditioning.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Every actual transported flag has norm at most two; the true transposed flag has the same spectral norm. Bound and sum the real compressed increment products.
-/
theorem obliqueStaircase_norm (T : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hT : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) :
    ‖obliqueStaircase T E F N‖≤4*(∑ l ∈ range N, ‖E l‖)+‖F‖ := by
  have hs : ‖∑ l ∈ range N, (transportedFlag T l)ᵀ*E l*transportedFlag T l‖≤4*∑ l ∈ range N, ‖E l‖ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ l ∈ range N, 4*‖E l‖ := by
        apply sum_le_sum
        intro l _hl
        have hp := transportedFlag_norm_two T hT l
        have ht := (norm_mul_le ((transportedFlag T l)ᵀ*E l) (transportedFlag T l)).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le (transportedFlag T l)ᵀ (E l)) (norm_nonneg _))
        rw [transpose_norm] at ht
        exact ht.trans ((mul_le_mul (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) hp
          (norm_nonneg _) (by positivity : (0 : ℝ)≤2*‖E l‖)).trans_eq (by ring))
      _ = _ := (mul_sum _ _ _).symm
  exact (norm_add_le _ _).trans ((add_le_add (le_refl _) hs).trans_eq (by ring))

/-- Changing both genuine compression flags has the stated dimension-free spectral product bound.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Telescope the actual two-sided product into its changed left and right factors, use genuine transpose norm invariance and the two supplied true flag bounds.
-/
theorem compression_sandwich_difference_norm (P Q E : Matrix (Fin n) (Fin n) ℝ)
    (hP : ‖P‖≤2) (hQ : ‖Q‖≤2) :
    ‖Pᵀ*E*P-Qᵀ*E*Q‖≤4*‖E‖*‖P-Q‖ := by
  have he : Pᵀ*E*P-Qᵀ*E*Q=(P-Q)ᵀ*E*P+Qᵀ*E*(P-Q) := by rw [transpose_sub]; noncomm_ring
  have h₁ : ‖(P-Q)ᵀ*E*P‖≤2*‖E‖*‖P-Q‖ := by
    calc
      _ ≤ (‖(P-Q)ᵀ‖*‖E‖)*‖P‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖P-Q‖*‖E‖)*2 := by rw [transpose_norm]; gcongr
      _ = _ := by ring
  have h₂ : ‖Qᵀ*E*(P-Q)‖≤2*‖E‖*‖P-Q‖ := by
    calc
      _ ≤ (‖Qᵀ‖*‖E‖)*‖P-Q‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (2*‖E‖)*‖P-Q‖ := by rw [transpose_norm]; gcongr
      _ = _ := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- The genuine reference-weighted staircase change is bounded by four times the real total increment budget and the actual weighted flag allowance.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: The common true terminal defect cancels. Keep the original reference weight on each real flag difference before applying the exact sandwich estimate and summing actual increment norms.
-/
theorem obliqueStaircase_weighted_difference (T Q : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hT : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) (hQ : ‖Qᵀ*Q-1‖≤(1/2 : ℝ))
    {w η : ℝ} (hw : 0≤w)
    (hflag : ∀ l<N, w*‖transportedFlag T l-transportedFlag Q l‖≤η) :
    w*‖obliqueStaircase T E F N-obliqueStaircase Q E F N‖≤4*(∑ l ∈ range N, ‖E l‖)*η := by
  have he : obliqueStaircase T E F N-obliqueStaircase Q E F N=
      ∑ l ∈ range N, ((transportedFlag T l)ᵀ*E l*transportedFlag T l-
        (transportedFlag Q l)ᵀ*E l*transportedFlag Q l) := by
    rw [sum_sub_distrib]
    unfold obliqueStaircase
    abel
  rw [he]
  calc
    _ ≤ w*∑ l ∈ range N, ‖(transportedFlag T l)ᵀ*E l*transportedFlag T l-
        (transportedFlag Q l)ᵀ*E l*transportedFlag Q l‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ l ∈ range N, w*‖(transportedFlag T l)ᵀ*E l*transportedFlag T l-
        (transportedFlag Q l)ᵀ*E l*transportedFlag Q l‖ := mul_sum _ _ _
    _ ≤ ∑ l ∈ range N, (4*‖E l‖)*η := by
      apply sum_le_sum
      intro l hl
      have ht := compression_sandwich_difference_norm (transportedFlag T l) (transportedFlag Q l) (E l)
        (transportedFlag_norm_two T hT l) (transportedFlag_norm_two Q hQ l)
      calc
        _ ≤ w*(4*‖E l‖*‖transportedFlag T l-transportedFlag Q l‖) := mul_le_mul_of_nonneg_left ht hw
        _ = (4*‖E l‖)*(w*‖transportedFlag T l-transportedFlag Q l‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hflag l (mem_range.mp hl)) (by positivity)
    _ = _ := by rw [← sum_mul,← mul_sum]

end
end krylov.Correction
