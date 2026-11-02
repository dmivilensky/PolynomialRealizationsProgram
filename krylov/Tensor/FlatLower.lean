import krylov.Tensor.FlatWitness

/-!
Article: main_krylov, apG:flat, the actual flat lower response.
Use: admit the printed genuine cubic witness to the original spectral ball
and evaluate the real last coordinate of the reversed flat response.
Source: the proved sharp unit-disk inequality and exact orthonormal sums.
-/

namespace krylov.Tensor
noncomputable section
open Finset krylov.Functions
open scoped BigOperators InnerProductSpace
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- The last actual prefix consists of exactly the preceding m frame vectors.
Article: main_krylov, apG:flat. -/
theorem flatPrefixVector_last (e : Fin (m+1) → E) :
    flatPrefixVector e (Fin.last m) = ∑ i : Fin m, e i.castSucc := by
  unfold flatPrefixVector
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_lt_last, ite_true, lt_self_iff_false, ite_false, add_zero]

/-- The actual last flat prefix has exactly its printed energy m.
Article: main_krylov, apG:flat. -/
theorem norm_flatPrefixVector_last_sq (e : Fin (m+1) → E) (he : Orthonormal ℝ e) :
    ‖flatPrefixVector e (Fin.last m)‖ ^ 2 = (m : ℝ) := by
  rw [flatPrefixVector_last]
  have hn := norm_orthonormal_sum (fun i : Fin m => e i.castSucc)
    (he.comp Fin.castSucc (Fin.castSucc_injective m)) univ
  simp only [card_univ, Fintype.card_fin] at hn
  rw [hn, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The last frame vector is genuinely orthogonal to its real flat prefix.
Article: main_krylov, apG:flat. -/
theorem inner_flatPrefixVector_last (e : Fin (m+1) → E) (he : Orthonormal ℝ e) :
    inner ℝ (e (Fin.last m)) (flatPrefixVector e (Fin.last m)) = 0 := by
  rw [flatPrefixVector_last, inner_sum]
  apply sum_eq_zero
  intro i _
  exact he.inner_eq_zero (by intro h; have := congrArg Fin.val h; simp only [Fin.val_last, Fin.val_castSucc] at this; have := i.isLt; omega)

/-- The normalized preceding-prefix witness belongs to the true diagonal
spectral ball and attains the printed flat lower response coordinate.
Article: main_krylov, apG:flat. -/
theorem flat_prefix_lower_witness (e : Fin (m+1) → E) (he : Orthonormal ℝ e) (hm : 1 ≤ m) :
    ∃ T : SymmetricCubic E,
      (∀ x : E, ‖x‖ = 1 → |T.form x x x| ≤ 2) ∧
      (Real.sqrt 3 / 2) * m ≤ ‖flatPrefixResponse e T‖ := by
  let a := e (Fin.last m)
  let v := flatPrefixVector e (Fin.last m)
  have hvsq : ‖v‖^2 = (m : ℝ) := norm_flatPrefixVector_last_sq e he
  have hv : v ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by decide)] at hvsq
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    linarith
  have ha : ‖a‖ = 1 := he.norm_eq_one _
  have hav : inner ℝ a v = 0 := inner_flatPrefixVector_last e he
  have han : inner ℝ a (NormedSpace.normalize v) = 0 := by
    simp only [NormedSpace.normalize, inner_smul_right, hav, mul_zero]
  have hnv : inner ℝ (NormedSpace.normalize v) v = ‖v‖ := by
    simp only [NormedSpace.normalize, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    field_simp
  let T := flatWitnessCubic (innerSL ℝ a) (innerSL ℝ (NormedSpace.normalize v))
  refine ⟨T, flatWitnessCubic_diagonal_bound a _ ha (NormedSpace.norm_normalize hv) han, ?_⟩
  have haa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
  have hna : inner ℝ (NormedSpace.normalize v) a = 0 := by rw [real_inner_comm]; exact han
  have hcoord : inner ℝ a (flatPrefixResponse e T) = (Real.sqrt 3 / 2) * m := by
    change inner ℝ (e (Fin.last m)) (∑ i : Fin (m+1), _ • e i) = _
    rw [he.inner_right_fintype]
    change (2 : ℝ)⁻¹ * ((flatWitnessForm _ _) a v v + (flatWitnessForm _ _) a a v) = _
    rw [flatWitnessForm_apply, flatWitnessForm_apply]
    simp only [innerSL_apply_apply, haa, hav, hna, hnv, one_mul, zero_mul, mul_zero,
      add_zero]
    rw [← pow_two, hvsq]
    ring
  have hb := real_inner_le_norm a (flatPrefixResponse e T)
  rw [hcoord, ha, one_mul] at hb
  exact hb

end
end krylov.Tensor
