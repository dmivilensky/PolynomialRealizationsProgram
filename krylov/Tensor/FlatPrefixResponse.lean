import krylov.Tensor.FlatPrefixBound

/-!
Article: main_krylov, apG:flat, actual normalized flat-profile response.
Use: combine the genuine dyadic squared-prefix estimate with the true
diagonal contraction estimate and obtain the printed logarithmic constant.
Source: Banach's identity, Bessel and the actual binary-prefix expansion.
-/

namespace krylov.Tensor
noncomputable section
open Finset krylov.Functions
open scoped BigOperators InnerProductSpace
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true flat-profile response after reversing the orthogonal coordinates.
Article: main_krylov, apG:flat, the direct sum for sym N_a. -/
def flatPrefixResponse (e : Fin N → E) (T : SymmetricCubic E) : E :=
  ∑ a : Fin N, ((2 : ℝ)⁻¹ * (T.form (e a) (flatPrefixVector e a) (flatPrefixVector e a) +
    T.form (e a) (e a) (flatPrefixVector e a))) • e a

/-- Every actual orthogonal prefix has norm at most sqrt n.
Article: main_krylov, apG:flat, the diagonal tensor term. -/
theorem norm_flatPrefixVector_le (e : Fin N → E) (he : Orthonormal ℝ e) (a : Fin N) :
    ‖flatPrefixVector e a‖ ≤ Real.sqrt (N : ℝ) := by
  have hp : flatPrefixVector e a = ∑ i ∈ univ.filter (fun i : Fin N => i < a), e i := by
    simp only [flatPrefixVector, sum_filter]
  rw [hp, norm_orthonormal_sum e he]
  apply Real.sqrt_le_sqrt
  exact_mod_cast (card_filter_le univ (fun i : Fin N => i < a)).trans_eq (card_univ.trans (Fintype.card_fin N))

/-- The actual coordinate absolute sum obeys the orthonormal Cauchy bound.
Article: main_krylov, apG:flat. -/
theorem flat_sum_abs_inner_le (e : Fin N → E) (he : Orthonormal ℝ e) (u : E) :
    ∑ a : Fin N, |inner ℝ (e a) u| ≤ Real.sqrt (N : ℝ) * ‖u‖ := by
  have hpart : Pairwise (fun a b : Fin N => Disjoint ({a} : Finset (Fin N)) {b}) := by
    intro a b hab
    simpa only [disjoint_singleton] using hab
  have hb := sum_norm_flagComponent_le e he (fun a : Fin N => {a}) hpart u
  simpa only [flagComponent, sum_singleton, norm_smul, Real.norm_eq_abs, he.norm_eq_one,
    mul_one, Fintype.card_fin] using hb

variable [FiniteDimensional ℝ E]

/-- The diagonal part of the actual flat contraction has cost at most n.
Article: main_krylov, apG:flat, the X₂ term; the slightly coarser bound n
suffices for the exact printed total constant ten. -/
theorem abs_flatPrefixDiagonal_le (e : Fin N → E) (he : Orthonormal ℝ e)
    (T : SymmetricCubic E) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x : E, ‖x‖ = 1 → |T.form x x x| ≤ C) (u : E) :
    |∑ a : Fin N, inner ℝ (e a) u * T.form (e a) (e a) (flatPrefixVector e a)| ≤ C * N * ‖u‖ := by
  calc
    _ ≤ ∑ a : Fin N, |inner ℝ (e a) u| * |T.form (e a) (e a) (flatPrefixVector e a)| := by
      simpa only [abs_mul] using abs_sum_le_sum_abs (fun a : Fin N =>
        inner ℝ (e a) u * T.form (e a) (e a) (flatPrefixVector e a)) univ
    _ ≤ ∑ a : Fin N, |inner ℝ (e a) u| * (C * Real.sqrt (N : ℝ)) := by
      apply sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hb := cubic_diagonal_bound T C hd (e a) (e a) (flatPrefixVector e a)
      simp only [he.norm_eq_one, mul_one] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left (norm_flatPrefixVector_le e he a) hC)
    _ = C * Real.sqrt (N : ℝ) * (∑ a : Fin N, |inner ℝ (e a) u|) := by rw [← sum_mul]; ring
    _ ≤ C * Real.sqrt (N : ℝ) * (Real.sqrt (N : ℝ) * ‖u‖) := by
      gcongr
      exact flat_sum_abs_inner_le e he u
    _ = _ := by
      calc
        _ = C * (Real.sqrt (N : ℝ)) ^ 2 * ‖u‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

omit [FiniteDimensional ℝ E] in
/-- Pairing the true flat response gives exactly the two actual contractions.
Article: main_krylov, apG:flat. -/
theorem inner_flatPrefixResponse (e : Fin N → E) (T : SymmetricCubic E) (u : E) :
    inner ℝ u (flatPrefixResponse e T) = (2 : ℝ)⁻¹ *
      (flatPrefixContraction e T u + ∑ a : Fin N, inner ℝ (e a) u *
        T.form (e a) (e a) (flatPrefixVector e a)) := by
  simp only [flatPrefixResponse, flatPrefixContraction, inner_sum, inner_smul_right]
  simp_rw [real_inner_comm u]
  simp only [mul_add, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro a _
  ring

/-- Every genuine spectral-budget-two cubic has the printed flat-profile
upper response estimate. Article: main_krylov, apG:flat.
Proof: normalize the true output, pair it with itself, and use the actual
dyadic decomposition, rather than a hypothesized nuclear estimate. -/
theorem norm_flatPrefixResponse_le (e : Fin N → E) (he : Orthonormal ℝ e)
    (T : SymmetricCubic E) (hd : ∀ x : E, ‖x‖ = 1 → |T.form x x x| ≤ 2)
    (hN : 2 ≤ N) : ‖flatPrefixResponse e T‖ ≤ 10 * N * Real.logb 2 (4 * N) := by
  have hcost := flat_dyadic_cost_log_bound hN
  have hq : 0 < Real.sqrt 2 - 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hp (u : E) : inner ℝ u (flatPrefixResponse e T) ≤
      (2 * (Nat.clog 2 N : ℝ) * (2 : ℝ) ^ Nat.clog 2 N / (Real.sqrt 2 - 1) + N) * ‖u‖ := by
    rw [inner_flatPrefixResponse]
    have h1 := abs_flatPrefixContraction_le e he T (by norm_num : (0 : ℝ) ≤ 2) hd
      (Nat.le_pow_clog (by decide : 1 < 2) N) u
    have h2 := abs_flatPrefixDiagonal_le e he T (by norm_num : (0 : ℝ) ≤ 2) hd u
    linarith [le_abs_self (flatPrefixContraction e T u),
      le_abs_self (∑ a : Fin N, inner ℝ (e a) u * T.form (e a) (e a) (flatPrefixVector e a))]
  by_cases hz : flatPrefixResponse e T = 0
  · rw [hz, norm_zero]
    exact (by positivity : (0 : ℝ) ≤ 2 * (Nat.clog 2 N : ℝ) *
      (2 : ℝ) ^ Nat.clog 2 N / (Real.sqrt 2 - 1) + N).trans hcost
  · have hb := hp (NormedSpace.normalize (flatPrefixResponse e T))
    have hi : inner ℝ (NormedSpace.normalize (flatPrefixResponse e T)) (flatPrefixResponse e T) =
        ‖flatPrefixResponse e T‖ := by
      simp only [NormedSpace.normalize, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
      field_simp
    rw [hi, NormedSpace.norm_normalize hz, mul_one] at hb
    exact hb.trans hcost

end
end krylov.Tensor
