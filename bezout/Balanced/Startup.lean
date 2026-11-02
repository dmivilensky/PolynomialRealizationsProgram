import bezout.Balanced.AlgorithmCoefficients

/-!
Article: bezout, Algorithm 2 startup impulse rows.
Use: the exact first three rows of the actual Balanced history are the printed
scalar preparation; no nominal coefficient identities are assumed.
Proof: expand the first stopped-parity polynomials and use graded-coordinate
uniqueness of each raw-query impulse row.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Explicit first raw query, valid for every Balanced horizon. -/
theorem rawQuery_zero (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    rawQuery I N hN ⟨0, by omega⟩ = 1 := by
  apply Polynomial.funext
  intro lam
  rw [rawQuery_eval]
  simp

/-- The physical initial query polynomial is exactly constant one. -/
theorem history_query_zero (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (history I N hN).query ⟨0, by omega⟩ = 1 := by
  simpa only [rawQuery, normalizer_zero, C_1, one_mul] using rawQuery_zero I N hN

/-- The first raw impulse is the initial Chebyshev gradient step. -/
theorem impulse_one (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (k : Fin N) : impulse I N hN ⟨1, by omega⟩ k = if k.val = 0 then -2 / I.delta else 0 := by
  let j0 : Fin N := ⟨0, by omega⟩
  have hc : impulse I N hN ⟨1, by omega⟩ =
      (fun t : Fin N => (-2 / I.delta) * if t = j0 then 1 else 0) := by
    apply impulse_unique
    apply Polynomial.funext
    intro lam
    simp only [rawQuery_eval, eval_add, eval_C, eval_mul, eval_X, eval_finsetSum]
    simp only [psi_one, T_one, eval_X, normalizer_one, mul_assoc, ← Finset.mul_sum,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      j0, history_query_zero, eval_one]
    rw [I.z_eq]
    ring
  have hk := congrFun hc k
  simpa only [j0, Fin.ext_iff, mul_ite, mul_one, mul_zero] using hk

/-- Startup normalizer at index two, as an exact scalar polynomial value. -/
theorem normalizer_two (I : chebyshev1.SpectralInterval) (N : ℕ) :
    normalizer I N 2 = 1 + omega N 2 * (2 * I.eta ^ 2 - 2) := by
  have h := normalizer_add_two I N 0
  norm_num only [normalizer_zero, Nat.reduceAdd, Nat.cast_zero, Nat.cast_ofNat,
    T_two, T_zero, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X, eval_one] at h
  rw [h]
  ring

/-- Startup query at index two, in exact polynomial-evaluation form. -/
theorem psi_two_eval (N : ℕ) (x : ℝ) :
    (psi N 2).eval x = 1 + omega N 2 * (2 * x ^ 2 - 2) := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (psi_add_two N 0)
  norm_num only [psi_zero, Nat.reduceAdd, Nat.cast_zero, Nat.cast_ofNat,
    T_two, T_zero, eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, eval_pow,
    eval_X, eval_one] at h
  rw [h]
  ring

/-- Both second-row impulses equal the displayed scalar preparation coefficient. -/
theorem impulse_two (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (h2 : 2 < N) (k : Fin N) :
    impulse I N hN ⟨2, h2⟩ k = if k.val < 2 then -4 * I.eta * omega N 2 / I.delta else 0 := by
  let j0 : Fin N := ⟨0, by omega⟩
  let j1 : Fin N := ⟨1, by omega⟩
  let H : ℝ := -4 * I.eta * omega N 2 / I.delta
  have hc : impulse I N hN ⟨2, h2⟩ = (fun t : Fin N =>
      H * (if t = j0 then 1 else 0) + H * (if t = j1 then 1 else 0)) := by
    apply impulse_unique
    apply Polynomial.funext
    intro lam
    simp only [rawQuery_eval, eval_add, eval_C, eval_mul, eval_X, eval_finsetSum,
      add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [j0, j1, history_query_eval, psi_zero, psi_one, T_one,
      eval_one, eval_X, normalizer_zero, normalizer_one, div_one, psi_two_eval, normalizer_two]
    rw [I.z_eq]
    dsimp [H]
    have heta := I.eta_gt_one
    field_simp
    ring
  have hk := congrFun hc k
  by_cases h0 : k.val = 0
  · have hk0 : k = j0 := Fin.ext h0
    simpa [hk0, j0, j1, H] using hk
  · by_cases h1 : k.val = 1
    · have hk1 : k = j1 := Fin.ext h1
      simpa [hk1, j0, j1, H] using hk
    · have hn0 : k ≠ j0 := by intro hh; exact h0 (congrArg Fin.val hh)
      have hn1 : k ≠ j1 := by intro hh; exact h1 (congrArg Fin.val hh)
      have hn2 : ¬k.val < 2 := by omega
      simpa [hn0, hn1, hn2] using hk

/-- The first third-row scalar preparation coefficient. -/
def startup30 (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  -2 / I.delta + omega N 3 * (-8 * I.eta ^ 2 / I.delta + 4 / (I.delta * omega N 2))

/-- The middle third-row scalar preparation coefficient. -/
def startup31 (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  -8 * I.eta ^ 2 * omega N 3 / I.delta

/-- The last third-row scalar preparation coefficient. -/
def startup32 (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  -4 * omega N 3 * normalizer I N 2 / (I.delta * omega N 2)

/-- Third stopped-parity query in a scalar chart. -/
theorem psi_three_eval (N : ℕ) (x : ℝ) :
    (psi N 3).eval x = x + omega N 3 * (4 * x ^ 3 - 4 * x) := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (psi_add_two N 1)
  have ht := congrArg (fun p : ℝ[X] => p.eval x) (T_add_two ℝ 1)
  norm_num only [psi_one, Nat.reduceAdd, Nat.cast_one, Nat.cast_ofNat,
    T_two, T_one, eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, eval_pow,
    eval_X, eval_one] at h ht
  linear_combination h + omega N 3 * ht

/-- All three third-row startup impulses are precisely the printed coefficients. -/
theorem impulse_three (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (h3 : 3 < N) (k : Fin N) :
    impulse I N hN ⟨3, h3⟩ k =
      startup30 I N * (if k.val = 0 then 1 else 0) +
      startup31 I N * (if k.val = 1 then 1 else 0) +
      startup32 I N * (if k.val = 2 then 1 else 0) := by
  let j0 : Fin N := ⟨0, by omega⟩
  let j1 : Fin N := ⟨1, by omega⟩
  let j2 : Fin N := ⟨2, by omega⟩
  have hc : impulse I N hN ⟨3, h3⟩ = (fun t : Fin N =>
      startup30 I N * (if t = j0 then 1 else 0) +
      startup31 I N * (if t = j1 then 1 else 0) +
      startup32 I N * (if t = j2 then 1 else 0)) := by
    apply impulse_unique
    apply Polynomial.funext
    intro lam
    simp only [rawQuery_eval, eval_add, eval_C, eval_mul, eval_X, eval_finsetSum,
      add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [j0, j1, j2, history_query_eval, psi_zero, psi_one, T_one,
      eval_one, eval_X, normalizer_zero, normalizer_one, div_one, psi_two_eval, psi_three_eval]
    have hZ3 : normalizer I N 3 = I.eta + omega N 3 * (4 * I.eta ^ 3 - 4 * I.eta) :=
      psi_three_eval N I.eta
    rw [hZ3]
    rw [I.z_eq]
    unfold startup30 startup31 startup32
    have hw := omega_pos hN (show 2 < N by omega)
    have hz := normalizer_pos I hN (show 2 < N by omega)
    have heta := I.eta_gt_one
    field_simp [ne_of_gt hz, ne_of_gt hw, ne_of_gt I.delta_pos, ne_of_gt (lt_trans zero_lt_one heta)]
    ring
  have hk := congrFun hc k
  simpa only [j0, j1, j2, Fin.ext_iff] using hk

end
end bezout.Balanced
