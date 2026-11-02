import krylov.Tensor.ReferenceFlatAmplification
import krylov.Tensor.FlatSqrtSum

/-!
Article: main_krylov, apG:flat, the exact actual operator coefficient.
Use: compute the genuine midpoint/tail budget under equal actual CG
energies and prove its printed three-halves lower bound.
Source: exact CG orthogonality and energies, followed by a genuine finite
square-root power sum bound.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual flat midpoint drift has its exact printed norm.
Article: main_krylov, apG:flat. -/
theorem reference_flat_midpoint_norm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hc : 0 ≤ c) (l : Fin (referenceAtomCount A hA g - 1)) :
    ‖referenceMidpointDrift A g l.val‖ = Real.sqrt c / Real.sqrt 2 := by
  have hl : l.val < referenceAtomCount A hA g := by have := l.isLt; omega
  have hl1 : l.val+1 < referenceAtomCount A hA g := by have := l.isLt; omega
  have h0 : ‖canonicalCGStep A g l.val‖^2 = c := (cgEnergy_eq_norm_sq A hA g _).symm.trans (hf ⟨_,hl⟩)
  have h1 : ‖canonicalCGStep A g (l.val+1)‖^2 = c := (cgEnergy_eq_norm_sq A hA g _).symm.trans (hf ⟨_,hl1⟩)
  have ho := canonicalCGStep_orth A hA g l.val (l.val+1) (by omega)
    (fun k hk => cg_nonstagnation A hA g k (by omega))
  have hn := norm_add_sq_real (canonicalCGStep A g l.val) (canonicalCGStep A g (l.val+1))
  rw [ho, h0, h1, mul_zero, add_zero] at hn
  have hsq : ‖referenceMidpointDrift A g l.val‖^2 = c/2 := by
    rw [referenceMidpointDrift, norm_smul, mul_pow]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    nlinarith only [hn]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt hc, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hsq

/-- The actual flat remaining tail has precisely its printed remaining-step norm.
Article: main_krylov, apG:flat. -/
theorem reference_flat_tail_norm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hc : 0 ≤ c) (l : Fin (referenceAtomCount A hA g - 1)) :
    ‖remainingTail A g l.val‖ = Real.sqrt c * Real.sqrt (referenceAtomCount A hA g - (l.val+1) : ℕ) := by
  have hl : l.val+1 ≤ referenceAtomCount A hA g := by have := l.isLt; omega
  have hs : ‖remainingTail A g l.val‖^2 = (referenceAtomCount A hA g - (l.val+1) : ℕ) * c := by
    rw [remainingTail_norm, cgEnergy_tail A hA g hl]
    calc
      _ = ∑ _j ∈ Ico (l.val+1) (referenceAtomCount A hA g), c := by
        apply sum_congr rfl
        intro j hj
        exact hf ⟨j, (mem_Ico.mp hj).2⟩
      _ = _ := by simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt (Nat.cast_nonneg _)]
  nlinarith only [hs]

/-- The actual chronological flat operator coefficient equals the exact
square-root sum printed in the article. Article: main_krylov, apG:flat. -/
theorem reference_flat_operator_eq (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hN : 2 ≤ referenceAtomCount A hA g) :
    referenceOperatorCoefficient A g (referenceAtomCount A hA g) =
      Real.sqrt 2 * c * ∑ j ∈ range (referenceAtomCount A hA g - 1), Real.sqrt (j+1 : ℕ) := by
  have hc := (flat_cg_energy_pos A hA g c hf (by omega)).le
  have hroot : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff (by positivity : Real.sqrt (2 : ℝ) ≠ 0)).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold referenceOperatorCoefficient
  calc
    _ = Real.sqrt 2 * c * ∑ l ∈ range (referenceAtomCount A hA g - 1),
        Real.sqrt (referenceAtomCount A hA g - (l+1) : ℕ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro l hl
      rw [reference_flat_midpoint_norm A hA g c hf hc ⟨l,mem_range.mp hl⟩,
        reference_flat_tail_norm A hA g c hf hc ⟨l,mem_range.mp hl⟩]
      calc
        _ = (2 / Real.sqrt 2) * (Real.sqrt c)^2 *
            Real.sqrt (referenceAtomCount A hA g - (l+1) : ℕ) := by ring
        _ = _ := by rw [hroot, Real.sq_sqrt hc]
    _ = _ := by
      congr 1
      rw [← sum_range_reflect (fun j => Real.sqrt (j+1 : ℕ))]
      apply sum_congr rfl
      intro l hl
      congr 2
      have := mem_range.mp hl
      omega

/-- The actual flat operator coefficient has the full printed three-halves
power lower bound. Article: main_krylov, apG:flat. -/
theorem reference_flat_operator_lower (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hN : 2 ≤ referenceAtomCount A hA g) :
    (2 * Real.sqrt 2 / 3) * c * ((referenceAtomCount A hA g - 1 : ℕ) : ℝ)^((3 : ℝ)/2) ≤
      referenceOperatorCoefficient A g (referenceAtomCount A hA g) := by
  have hc := (flat_cg_energy_pos A hA g c hf (by omega)).le
  rw [reference_flat_operator_eq A hA g c hf hN]
  have hb := mul_le_mul_of_nonneg_left (flat_sqrt_sum_lower (referenceAtomCount A hA g - 1))
    (mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hc)
  convert hb using 1
  ring

end
end krylov.Tensor
