import krylov.Tensor.FlagResponse
import krylov.Variation.ReferenceFlags

/-!
Article: main_krylov, thm:Hp, the actual CG energy-profile upper bound.
Use: derive the printed independent-operator coefficient directly from the
computed reference steps, errors and true midpoint differences.
Source: exact CG Pythagoras and monotonicity of its actual energy error.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual adjacent CG segment midpoints differ by half their two actual steps.
Article: main_krylov, thm:Htransfer and thm:Hp. -/
def referenceMidpointDrift (A : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (1 / 2 : ℝ) • (canonicalCGStep A g l + canonicalCGStep A g (l + 1))

/-- The actual canonical error norm decreases along the entire genuine CG run.
Article: main_krylov, thm:Hp.
Proof: each true energy drop is the squared norm of the computed step. -/
theorem reference_error_antitone (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) : Antitone (fun l => ‖cgCanonicalError A g l‖) := by
  apply antitone_nat_of_succ_le
  intro l
  have hd := cgEnergy_drop A hA g l
  rw [cgEnergy_eq_norm_sq A hA] at hd
  nlinarith [norm_nonneg (cgCanonicalError A g l), norm_nonneg (cgCanonicalError A g (l+1)),
    sq_nonneg ‖canonicalCGStep A g l‖]

/-- The true doubled midpoint drift is bounded by the true current energy error.
Article: main_krylov, thm:Hp, 2 norm(xi_l) ≤ norm(e_l).
Proof: two successive actual orthogonal step energies telescope to the
current squared error minus the nonnegative squared error two steps later. -/
theorem reference_midpoint_drift_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) (hl : l+1 < referenceAtomCount A hA g) :
    2 * ‖referenceMidpointDrift A g l‖ ≤ ‖cgCanonicalError A g l‖ := by
  have ho := canonicalCGStep_orth A hA g l (l+1) (by omega)
    (fun k hk => cg_nonstagnation A hA g k (by omega))
  have hnorm := norm_add_sq_real (canonicalCGStep A g l) (canonicalCGStep A g (l+1))
  rw [ho, mul_zero, add_zero] at hnorm
  have hd₀ := cgEnergy_drop A hA g l
  have hd₁ := cgEnergy_drop A hA g (l+1)
  rw [cgEnergy_eq_norm_sq A hA] at hd₀ hd₁
  have hle : ‖canonicalCGStep A g l + canonicalCGStep A g (l+1)‖ ≤ ‖cgCanonicalError A g l‖ := by
    nlinarith [norm_nonneg (canonicalCGStep A g l + canonicalCGStep A g (l+1)),
      norm_nonneg (cgCanonicalError A g l), sq_nonneg ‖cgCanonicalError A g (l+1+1)‖]
  rw [referenceMidpointDrift, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  linarith

/-- The independent-operator coefficient of the actual compatible CG midpoint increments.
Article: main_krylov, thm:Hp, Gamma_op. -/
def referenceOperatorCoefficient (A : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) : ℝ :=
  ∑ l ∈ range (N-1), 2 * ‖referenceMidpointDrift A g l‖ * ‖remainingTail A g l‖

/-- The actual operator coefficient has the printed two-error profile bound.
Article: main_krylov, thm:Hp, final displayed inequality.
Proof: separate the first genuine segment; all later errors and tails are
bounded by the genuine first post-search error by CG energy monotonicity. -/
theorem reference_operator_coefficient_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2 ≤ N)
    (hcount : N ≤ referenceAtomCount A hA g) :
    referenceOperatorCoefficient A g N ≤
      ‖cgCanonicalError A g 0‖ * ‖cgCanonicalError A g 1‖ +
        (N-2 : ℕ) * ‖cgCanonicalError A g 1‖ ^ 2 := by
  have hm := reference_error_antitone A hA g
  have hidx : N-1 = (N-2)+1 := by omega
  unfold referenceOperatorCoefficient
  rw [hidx, sum_range_succ']
  have hfirst : 2 * ‖referenceMidpointDrift A g 0‖ * ‖remainingTail A g 0‖ ≤
      ‖cgCanonicalError A g 0‖ * ‖cgCanonicalError A g 1‖ := by
    rw [remainingTail_norm]
    exact mul_le_mul_of_nonneg_right (reference_midpoint_drift_le A hA g 0 (by omega)) (norm_nonneg _)
  have hrest : (∑ l ∈ range (N-2),
      2 * ‖referenceMidpointDrift A g (l+1)‖ * ‖remainingTail A g (l+1)‖) ≤
      (N-2 : ℕ) * ‖cgCanonicalError A g 1‖ ^ 2 := by
    calc
      _ ≤ ∑ _l ∈ range (N-2), ‖cgCanonicalError A g 1‖ ^ 2 := by
        apply sum_le_sum
        intro l hl
        have hmid := (reference_midpoint_drift_le A hA g (l+1) (by simp only [mem_range] at hl; omega)).trans
          (hm (show 1 ≤ l+1 by omega))
        rw [remainingTail_norm]
        have htail := hm (show 1 ≤ l+1+1 by omega)
        nlinarith [norm_nonneg (referenceMidpointDrift A g (l+1)),
          norm_nonneg (cgCanonicalError A g (l+1+1)), norm_nonneg (cgCanonicalError A g 1)]
      _ = _ := by simp [nsmul_eq_mul]
  linarith

end
end krylov.Tensor
