import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.BigOperators.Field

/-! The reciprocal weight involution in logarithmic coordinates. -/
namespace chebyshev1.WeightCoordinates
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Reciprocal weight reversal with prescribed positive square root weights `p`. -/
def reverse (p w : ι → ℝ) (j : ι) : ℝ :=
  (p j ^ 2 / w j) / ∑ k, p k ^ 2 / w k

/-- Logarithmic coordinates centered at the normalized weights proportional to `p`. -/
def logWeights (p x : ι → ℝ) (j : ι) : ℝ :=
  (p j * Real.exp (x j)) / ∑ k, p k * Real.exp (x k)

theorem logWeights_pos (p x : ι → ℝ) (hp : ∀ j, 0 < p j) (j : ι) :
    0 < logWeights p x j := by
  exact div_pos (mul_pos (hp j) (Real.exp_pos _))
    (Finset.sum_pos (fun k _ => mul_pos (hp k) (Real.exp_pos _)) Finset.univ_nonempty)

theorem logWeights_sum (p x : ι → ℝ) (hp : ∀ j, 0 < p j) :
    ∑ j, logWeights p x j = 1 := by
  unfold logWeights
  rw [← Finset.sum_div, div_self]
  exact (Finset.sum_pos (fun k _ => mul_pos (hp k) (Real.exp_pos _)) Finset.univ_nonempty).ne'

theorem reverse_logWeights (p x : ι → ℝ) (hp : ∀ j, 0 < p j) :
    reverse p (logWeights p x) = logWeights p (-x) := by
  have hs : (∑ k, p k * Real.exp (x k)) ≠ 0 :=
    (Finset.sum_pos (fun k _ => mul_pos (hp k) (Real.exp_pos _)) Finset.univ_nonempty).ne'
  have ht : (∑ k, p k * Real.exp (-x k)) ≠ 0 :=
    (Finset.sum_pos (fun k _ => mul_pos (hp k) (Real.exp_pos _)) Finset.univ_nonempty).ne'
  have he (j : ι) : p j ^ 2 / logWeights p x j =
      (∑ k, p k * Real.exp (x k)) * (p j * Real.exp (-x j)) := by
    unfold logWeights
    rw [Real.exp_neg]
    field_simp [(hp j).ne', Real.exp_ne_zero, hs]
  funext j
  unfold reverse
  simp_rw [he]
  rw [← Finset.mul_sum]
  simp only [logWeights, Pi.neg_apply]
  field_simp [hs, ht]

/-- The normalized square root weights are fixed by reversal. -/
theorem reverse_fixed_weights (p : ι → ℝ) (hp : ∀ j, 0 < p j) :
    reverse p (fun j => p j / ∑ k, p k) = fun j => p j / ∑ k, p k := by
  have h := reverse_logWeights p 0 hp
  have hz : logWeights p 0 = fun j => p j / ∑ k, p k := by
    funext j
    simp [logWeights]
  simpa only [neg_zero, hz] using h

/-- Among positive probability weights the reversal fixed point is unique. -/
theorem reverse_fixed_iff (p w : ι → ℝ) (hp : ∀ j, 0 < p j)
    (hw : ∀ j, 0 < w j) (hwsum : (∑ j, w j) = 1) :
    reverse p w = w ↔ w = fun j => p j / ∑ k, p k := by
  constructor
  · intro hfix
    let S : ℝ := ∑ k, p k ^ 2 / w k
    have hs : 0 < S :=
      Finset.sum_pos (fun k _ => div_pos (sq_pos_of_pos (hp k)) (hw k)) Finset.univ_nonempty
    have hline (j : ι) : p j = w j * Real.sqrt S := by
      have he := congrFun hfix j
      change p j ^ 2 / w j / S = w j at he
      have heq : p j ^ 2 = (w j) ^ 2 * S := by
        field_simp [(hw j).ne', hs.ne'] at he
        nlinarith [he]
      apply (sq_eq_sq₀ (hp j).le (mul_nonneg (hw j).le (Real.sqrt_nonneg S))).mp
      rw [mul_pow, Real.sq_sqrt hs.le, heq]
    have hsum : (∑ j, p j) = Real.sqrt S := by
      simp_rw [hline]
      rw [← Finset.sum_mul, hwsum, one_mul]
    funext j
    apply (eq_div_iff (hsum.trans_ne (Real.sqrt_pos.mpr hs).ne')).mpr
    rw [hsum, ← hline]
  · rintro rfl
    exact reverse_fixed_weights p hp

/-- An even differentiable functional has zero differential at the origin. -/
theorem differential_zero_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (L : E →L[ℝ] ℝ) (hF : HasFDerivAt F L 0)
    (heven : ∀ x, F (-x) = F x) : L = 0 := by
  have hf' : HasFDerivAt F L ((-id) (0 : E)) := by simpa using hF
  have hneg := hf'.comp (0 : E) ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).neg)
  have heq : (fun x => F (-x)) = F := funext heven
  change HasFDerivAt (fun x : E => F (-x))
    (L.comp (-ContinuousLinearMap.id ℝ E)) 0 at hneg
  rw [heq] at hneg
  have hL := hneg.unique hF
  ext x
  have hx := congrArg (fun A : E →L[ℝ] ℝ => A x) hL
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at hx
  simpa using (show L x = 0 by linarith)

/-- Every differentiable reversal-invariant functional is stationary in centered log weights. -/
theorem stationary_logWeights (p : ι → ℝ) (hp : ∀ j, 0 < p j)
    (F : (ι → ℝ) → ℝ) (L : (ι → ℝ) →L[ℝ] ℝ)
    (hF : HasFDerivAt (fun x => F (logWeights p x)) L 0)
    (hinvariant : ∀ w, (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      F (reverse p w) = F w) : L = 0 := by
  apply differential_zero_of_even (fun x => F (logWeights p x)) L hF
  intro x
  rw [← reverse_logWeights p x hp]
  exact hinvariant _ (logWeights_pos p x hp) (logWeights_sum p x hp)

end
end chebyshev1.WeightCoordinates
