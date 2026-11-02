import bezout.Flat.History

/-!
Article: bezout, Equation (12) (`eq:hall-flat`) and Theorem 3.1.
Use: the actual Flat history has one common sharp physical response bound at
all calls, attained simultaneously at the lower spectral endpoint.
Proof: the explicit source-mass formula converts normalized convex factors
to S_N/N, and each factor has modulus at most one with endpoint value one.
-/

namespace bezout.Flat
noncomputable section
open Polynomial
open scoped BigOperators

/-- The common normalized source mass has exactly the article's physical scale.
Use: converts the explicit Flat responses to S_N/N. -/
theorem physical_unitMass (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    4 * I.epsilon N / I.delta * unitMass I N = bezout.Lower.additiveScale I N / N := by
  unfold unitMass
  rw [totalMass_formula I N hN]
  unfold bezout.Lower.additiveScale chebyshev1.SpectralInterval.epsilon
  have hd := ne_of_gt I.delta_pos
  have hm := ne_of_gt I.mu_pos
  have he := ne_of_gt (sub_pos.mpr I.eta_gt_one)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have heta : (I.eta - 1) * I.delta = 2 * I.mu := by
    unfold chebyshev1.SpectralInterval.eta
    field_simp [hd]
    unfold chebyshev1.SpectralInterval.delta
    ring
  field_simp [I.den_ne N, hd, hm, he, hn]
  linear_combination -2 * (I.den N - 1) * heta

/-- The exact Flat physical response is S_N/N times a convex Chebyshev mixture.
Use: deterministic and martingale estimates share this same response formula. -/
theorem response_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) :
    ((history I N hN).response s).eval lam =
      -(bezout.Lower.additiveScale I N / N) *
        (factorPolynomial I N (N - 1 - s.val)).eval (I.z lam) := by
  rw [history_response_eval]
  have hs := physical_unitMass I N (by omega)
  calc
    _ = -(4 * I.epsilon N / I.delta * unitMass I N) *
        (factorPolynomial I N (N - 1 - s.val)).eval (I.z lam) := by ring
    _ = _ := by rw [hs]

/-- Every physical Flat response has modulus bounded by the common optimum scale.
Use: a dimension-free per-call upper bound on every admissible Hessian. -/
theorem response_abs_le (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) {lam : ℝ} (hlam : lam ∈ Set.Icc I.mu I.L) :
    |((history I N hN).response s).eval lam| ≤ bezout.Lower.additiveScale I N / N := by
  have hs := physical_unitMass I N (by omega)
  have hc : 0 ≤ bezout.Lower.additiveScale I N / N := by
    rw [← hs]
    exact le_of_lt (mul_pos (div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos)
      (unitMass_pos I N (by omega)))
  rw [response_eval, abs_mul, abs_neg, abs_of_nonneg hc]
  have hf := factorPolynomial_abs_le I N (by omega) (N - 1 - s.val) (by omega)
    (I.z lam) (abs_le.mpr (I.z_mem hlam))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf hc

/-- Every physical response attains the same negative value at mu.
Use: simultaneous endpoint sharpness, including independent per-call noise. -/
theorem response_mu (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) :
    ((history I N hN).response s).eval I.mu = -(bezout.Lower.additiveScale I N / N) := by
  rw [response_eval, I.z_mu, factorPolynomial_one, mul_one]

/-- The per-call response bound is sharp on the entire admissible interval.
Use: the exact equal-response assertion of the Flat construction. -/
theorem response_uniform_sharp (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) :
    (∀ lam ∈ Set.Icc I.mu I.L, |((history I N hN).response s).eval lam| ≤
      bezout.Lower.additiveScale I N / N) ∧
    ((history I N hN).response s).eval I.mu = -(bezout.Lower.additiveScale I N / N) :=
  ⟨fun _ hlam => response_abs_le I N hN s hlam, response_mu I N hN s⟩

end
end bezout.Flat
