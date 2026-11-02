import bezout.Comparisons.Classical.History
import bezout.Risk.Bounds
import chebyshev1.Prefix.Kernel

/-!
Article: bezout, classical response factors in Appendix B.
Use: sharp actual Prefix response/query bounds with simultaneous endpoint
attainment and agreement with the original two-state insertion kernel.
Proof: first-kind and second-kind bounds and exact physical scaling.
-/

namespace bezout.Classical
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Both startup and subsequent Hall weights are positive. -/
theorem initialWeight_pos (s : ℕ) : 0 < initialWeight s := by
  unfold initialWeight
  split_ifs <;> norm_num

/-- Response degree plus one is its remaining-call length. -/
theorem response_length {N : ℕ} (s : Fin N) :
    ((N - 1 - s.val : ℕ) : ℝ) + 1 = (N : ℝ) - s.val := by
  have hn : N - 1 - s.val + 1 = N - s.val := by omega
  have hc : ((N - 1 - s.val : ℕ) : ℝ) + 1 = ((N - s.val : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hr : ((N - s.val : ℕ) : ℝ) = (N : ℝ) - s.val := Nat.cast_sub (by omega)
  exact hc.trans hr

/-- The sharp physical response modulus. -/
def responseBound (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  (4 * I.epsilon N / I.delta) * (initialWeight s * I.den s) * ((N : ℝ) - s)

/-- The sharp normalized query modulus. -/
def queryBound (I : chebyshev1.SpectralInterval) (s : ℕ) : ℝ := 1 / I.den s

/-- Every actual response bound is positive. -/
theorem responseBound_pos (I : chebyshev1.SpectralInterval) {N : ℕ} (s : Fin N) :
    0 < responseBound I N s := by
  have hn : (0 : ℝ) < (N : ℝ) - s.val := sub_pos.mpr (by exact_mod_cast s.isLt)
  have he := one_div_pos.mpr (I.den_pos N)
  have hd := I.delta_pos
  have hw := initialWeight_pos s
  have hp := I.den_pos s
  unfold responseBound
  positivity

/-- Every query bound is positive. -/
theorem queryBound_pos (I : chebyshev1.SpectralInterval) (s : ℕ) :
    0 < queryBound I s := one_div_pos.mpr (I.den_pos s)

/-- The entire spectral interval satisfies the sharp response bound. -/
theorem response_bound (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) {lam : ℝ} (hlam : lam ∈ Set.Icc I.mu I.L) :
    |((history I N).response s).eval lam| ≤ responseBound I N s := by
  have hc : 0 < 4 * I.epsilon N / I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  have hw := mul_pos (initialWeight_pos s) (I.den_pos s)
  have hu := chebyshev1.abs_U_eval_le (N - 1 - s.val) (abs_le.mpr (I.z_mem hlam))
  rw [response_length s] at hu
  rw [response_eval I N hN, abs_mul, abs_mul]
  have hneg : |-4 * I.epsilon N / I.delta| = 4 * I.epsilon N / I.delta := by
    rw [show -4 * I.epsilon N / I.delta = -(4 * I.epsilon N / I.delta) by ring,
      abs_neg, abs_of_pos hc]
  rw [hneg, abs_of_pos hw]
  exact mul_le_mul_of_nonneg_left hu (mul_pos hc hw).le

/-- The entire spectral interval satisfies the sharp query bound. -/
theorem query_bound (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N)
    {lam : ℝ} (hlam : lam ∈ Set.Icc I.mu I.L) :
    |((history I N).query s).eval lam| ≤ queryBound I s := by
  rw [query_eval, abs_div, abs_of_pos (I.den_pos s)]
  exact div_le_div_of_nonneg_right
    (abs_eval_T_real_le_one (s.val : ℤ) (abs_le.mpr (I.z_mem hlam))) (I.den_pos s).le

/-- The lower endpoint attains each signed response modulus. -/
theorem response_endpoint (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) : ((history I N).response s).eval I.mu = -responseBound I N s := by
  rw [response_eval I N hN, I.z_mu, U_eval_one]
  simp only [Int.cast_natCast, response_length s]
  unfold responseBound
  ring

/-- The lower endpoint attains every query modulus simultaneously. -/
theorem query_endpoint (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) :
    ((history I N).query s).eval I.mu = queryBound I s := by
  rw [query_eval, I.z_mu, T_eval_one]
  rfl

/-- Actual response bounds form the uniform certificate used by all risk estimates. -/
theorem responseBounds (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    bezout.Risk.ResponseBounds (history I N) I (fun s => responseBound I N s) :=
  ⟨fun s => (responseBound_pos I s).le, fun s _ hx => response_bound I N hN s hx⟩

/-- Query normalization cancels from each response-query product. -/
theorem bound_product (I : chebyshev1.SpectralInterval) (N s : ℕ) :
    responseBound I N s * queryBound I s =
      (4 * I.epsilon N / I.delta) * initialWeight s * ((N : ℝ) - s) := by
  unfold responseBound queryBound
  field_simp [I.den_ne s]

/-- The actual physical kernel is the original two-state Prefix insertion kernel. -/
theorem physicalKernel_eq_prefix (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) (x y : ℝ) :
    Lower.physicalKernel (history I N) s x y = (chebyshev1.Prefix.realization I).kernel N s.val x y := by
  rw [Lower.physicalKernel, response_eval I N hN, query_eval]
  rcases s with ⟨s, hs⟩
  cases s with
  | zero =>
    rw [chebyshev1.Prefix.kernel_zero I N (by omega)]
    simp only [initialWeight, ite_true, Nat.cast_zero, T_zero, eval_one]
    have hd : I.den 0 = 1 := by simp [chebyshev1.SpectralInterval.den]
    rw [hd]
    have hind : ((N - 1 - 0 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    rw [hind]
    unfold chebyshev1.SpectralInterval.epsilon
    ring
  | succ s =>
    rw [chebyshev1.Prefix.kernel_succ I N s hs]
    simp only [initialWeight, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      one_mul, show N - 1 - (s + 1) = N - (s + 2) by omega]
    unfold chebyshev1.SpectralInterval.epsilon
    have hind : ((N - (s + 2) : ℕ) : ℤ) = (N : ℤ) - ((s : ℤ) + 2) := by omega
    have hT : ((s + 1 : ℕ) : ℤ) = (s : ℤ) + 1 := by omega
    rw [hind, hT]
    field_simp [I.den_ne (s + 1)]

end
end bezout.Classical
