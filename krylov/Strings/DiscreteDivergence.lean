import krylov.Strings.DiscreteOperator

/-!
Article: `main_krylov`, `apC:lem:stieltjes`, literal weighted path equations.
Compute the actual rank-one energy operator as a discrete divergence of
physical edge fluxes. These identities connect the independently constructed
positive operator to the source Stieltjes polynomial and top recurrences.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- A finite edge-index delta sum is its actual physical site contribution. -/
theorem sum_edge_site (f : Fin N → ℝ) (r : ℕ) :
    (∑ k : Fin N, if k.val = r then f k else 0) =
      if hr : r < N then f ⟨r, hr⟩ else 0 := by
  by_cases hr : r < N
  · rw [dite_eq_left hr]
    have he (k : Fin N) : k.val = r ↔ k = (⟨r, hr⟩ : Fin N) := by
      constructor
      · intro h
        apply Fin.ext
        exact h
      · exact congrArg Fin.val
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [dite_eq_right hr]
    apply Finset.sum_eq_zero
    intro k _
    exact ite_eq_right (by omega)

/-- The mass-normalized incidence vectors are the literal two-sided physical
discrete divergence, including the first and last sites. -/
theorem sum_edgeVector (i : Fin (N + 1)) (f : Fin N → ℝ) :
    (∑ k : Fin N, S.edgeVector k i * f k) =
      (if hi : i.val < N then (Real.sqrt (S.mass i.val))⁻¹ * f ⟨i.val, hi⟩ else 0) -
        (if hi : 0 < i.val then
          (Real.sqrt (S.mass i.val))⁻¹ * f ⟨i.val - 1, by omega⟩ else 0) := by
  simp only [edgeVector, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  have ho : (∑ k : Fin N, if i.val = k.val then (Real.sqrt (S.mass i.val))⁻¹ * f k else 0) =
      if hi : i.val < N then (Real.sqrt (S.mass i.val))⁻¹ * f ⟨i.val, hi⟩ else 0 := by
    simpa only [eq_comm] using sum_edge_site (fun k ↦ (Real.sqrt (S.mass i.val))⁻¹ * f k) i.val
  rw [ho]
  congr 1
  by_cases hi : 0 < i.val
  · rw [dite_eq_left hi]
    have he (k : Fin N) : i.val = k.val + 1 ↔ k.val = i.val - 1 := by omega
    simp_rw [he]
    rw [sum_edge_site, dite_eq_left (show i.val - 1 < N by omega)]
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro k _
    exact ite_eq_right (by omega)

/-- Actual physical values embedded in the symmetric mass coordinates. -/
def massEmbedding (u : ℕ → ℝ) (i : Fin (N + 1)) : ℝ := Real.sqrt (S.mass i.val) * u i.val

/-- The incidence vector reads the exact physical difference across its
own true edge; normalization cancels only strictly positive actual masses. -/
theorem edge_dot_massEmbedding (k : Fin N) (u : ℕ → ℝ) :
    S.edgeVector k ⬝ᵥ S.massEmbedding u = u k.val - u (k.val + 1) := by
  let i : Fin (N + 1) := k.castSucc
  let j : Fin (N + 1) := k.succ
  have hi : Real.sqrt (S.mass k.val) ≠ 0 := (Real.sqrt_pos.mpr (S.mass_pos k.val (by omega))).ne'
  have hj : Real.sqrt (S.mass (k.val + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (S.mass_pos (k.val + 1) (by omega))).ne'
  simp only [dotProduct, edgeVector, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  have he₀ (r : Fin (N + 1)) : r.val = k.val ↔ r = i := by
    constructor
    · intro h
      apply Fin.ext
      exact h
    · exact congrArg Fin.val
  have he₁ (r : Fin (N + 1)) : r.val = k.val + 1 ↔ r = j := by
    constructor
    · intro h
      apply Fin.ext
      exact h
    · exact congrArg Fin.val
  simp only [he₀, he₁, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (Real.sqrt (S.mass k.val))⁻¹ * (Real.sqrt (S.mass k.val) * u k.val) -
    (Real.sqrt (S.mass (k.val + 1)))⁻¹ * (Real.sqrt (S.mass (k.val + 1)) * u (k.val + 1)) = _
  simp only [← mul_assoc, inv_mul_cancel₀ hi, inv_mul_cancel₀ hj, one_mul]

/-- The actual last boundary functional reads its physical site value. -/
theorem last_dot_massEmbedding (u : ℕ → ℝ) : S.lastVector ⬝ᵥ S.massEmbedding u = u N := by
  have he (r : Fin (N + 1)) : r.val = N ↔ r = Fin.last N := by
    constructor
    · intro h
      apply Fin.ext
      exact h
    · exact congrArg Fin.val
  simp only [dotProduct, lastVector, ite_mul, zero_mul, he,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (Real.sqrt (S.mass N))⁻¹ * (Real.sqrt (S.mass N) * u N) = _
  rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (S.mass_pos N le_rfl)).ne', one_mul]

/-- Actual operator action expressed in its true physical edge energies. -/
theorem operator_mulVec_action (x : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    (S.operator *ᵥ x) i =
      (∑ k : Fin N, S.edgeVector k i * ((S.gap k.val)⁻¹ * (S.edgeVector k ⬝ᵥ x))) +
        S.robin * S.lastVector i * (S.lastVector ⬝ᵥ x) := by
  simp only [operator, mulVec, dotProduct, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- Exact source weighted-path difference equation for the constructed
physical operator, including its first and Robin endpoint rows. -/
theorem operator_massEmbedding_action (u : ℕ → ℝ) (i : Fin (N + 1)) :
    (S.operator *ᵥ S.massEmbedding u) i =
      (if i.val < N then (Real.sqrt (S.mass i.val))⁻¹ *
        ((S.gap i.val)⁻¹ * (u i.val - u (i.val + 1))) else 0) -
      (if 0 < i.val then (Real.sqrt (S.mass i.val))⁻¹ *
        ((S.gap (i.val - 1))⁻¹ * (u (i.val - 1) - u i.val)) else 0) +
      (if i.val = N then S.robin * (Real.sqrt (S.mass i.val))⁻¹ * u i.val else 0) := by
  rw [operator_mulVec_action]
  simp_rw [edge_dot_massEmbedding]
  rw [sum_edgeVector, last_dot_massEmbedding]
  by_cases hp : 0 < i.val
  · have hpred : i.val - 1 + 1 = i.val := by omega
    simp only [dite_eq_left hp, ite_eq_left hp, hpred]
    by_cases ht : i.val = N
    · simp [lastVector, ht]
    · simp [lastVector, ht]
  · simp only [dite_eq_right hp, ite_eq_right hp]
    by_cases ht : i.val = N
    · have hN : N = 0 := by omega
      simp [lastVector, ht, hN]
    · simp [lastVector, ht]

/-- The actual physical diagonal contains exactly the two incident edge
conductances and the possible terminal Robin contribution. -/
theorem operator_diagonal (i : Fin (N + 1)) :
    S.operator i i =
      (if i.val < N then (S.gap i.val)⁻¹ * (S.mass i.val)⁻¹ else 0) +
      (if 0 < i.val then (S.gap (i.val - 1))⁻¹ * (S.mass i.val)⁻¹ else 0) +
      (if i.val = N then S.robin * (S.mass i.val)⁻¹ else 0) := by
  have hq : ((Real.sqrt (S.mass i.val))⁻¹) ^ 2 = (S.mass i.val)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (S.mass_pos i.val (by omega)).le]
  have he : S.operator i i =
      (∑ k : Fin N, S.edgeVector k i * ((S.gap k.val)⁻¹ * S.edgeVector k i)) +
        S.robin * S.lastVector i ^ 2 := by
    simp only [operator, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, vecMulVec_apply, pow_two]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, sum_edgeVector]
  simp_rw [← hq]
  by_cases hp : 0 < i.val
  · have hpred : i.val - 1 + 1 = i.val := by omega
    have hne : i.val ≠ i.val - 1 := by omega
    simp only [dite_eq_left hp, ite_eq_left hp, edgeVector, hpred,
      ite_eq_right hne, ite_true, zero_sub]
    by_cases hr : i.val < N
    · simp only [dite_eq_left hr, ite_eq_left hr,
        ite_eq_right (show i.val ≠ i.val + 1 by omega), sub_zero]
      by_cases ht : i.val = N <;> simp only [lastVector, ht, ite_true, ite_false, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] <;>
        ring
    · simp only [dite_eq_right hr, ite_eq_right hr]
      by_cases ht : i.val = N <;> simp only [lastVector, ht, ite_true, ite_false, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] <;>
        ring
  · simp only [dite_eq_right hp, ite_eq_right hp, sub_zero, add_zero]
    by_cases hr : i.val < N
    · simp only [dite_eq_left hr, ite_eq_left hr, edgeVector,
        ite_true, ite_eq_right (show i.val ≠ i.val + 1 by omega), sub_zero]
      by_cases ht : i.val = N <;> simp only [lastVector, ht, ite_true, ite_false, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] <;>
        ring
    · simp only [dite_eq_right hr, ite_eq_right hr]
      by_cases ht : i.val = N <;> simp only [lastVector, ht, ite_true, ite_false, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]

end
end krylov.Strings.DiscreteString
