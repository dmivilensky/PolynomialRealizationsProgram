import bezout.Balanced.ResponsePositivity
import bezout.Balanced.Energy
import bezout.Synthesis.Theorem

/-!
Article: bezout, Theorem `thm:linear` and Equations `eq:linear-balance` and
`eq:stopped-gain`.
Use: the actual Balanced history has proved physical response and query bounds,
attained simultaneously at mu; their squared products equal the exact optimum.
Proof: unique separated factors, positive Chebyshev coefficient bounds and the
exact finite parity-mass calculation.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial
open scoped BigOperators

/-- The eta-normalized separated response factor in the Chebyshev chart. -/
def responseFactor (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  C (normalizer I N s) * factor N s

/-- The normalized Balanced factors give the exact full-plane Bezoutian. -/
theorem tensor_identity (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (x y : ℝ) :
    (∑ s : Fin N, (responseFactor I N s).eval x *
      ((queryFamily I N hN).poly s).eval y) = chebyshevBezout N x y := by
  calc
    _ = ∑ s : Fin N, (factor N s).eval x * (psi N s).eval y := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [responseFactor, queryFamily, eval_mul, eval_C]
      have hz := ne_of_gt (normalizer_pos I hN s.isLt)
      field_simp
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => (factor N s).eval x * (psi N s).eval y) N]
      exact factorization N hN x y

/-- The actual physical response factors are exactly the constructed positive factors. -/
theorem history_chartFactor (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (history I N hN).chartFactor I s = responseFactor I N s := by
  have hf := (history I N hN).chart_factors_unique I (by omega) (history_exact I N hN)
    (fun t => responseFactor I N t) (fun x y => by
      simp only [history_chartQuery]
      exact tensor_identity I N hN x y)
  exact (congrFun hf s).symm

/-- The constructed physical responses have the exact article scaling and sign. -/
theorem history_response_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) :
    ((history I N hN).response s).eval lam =
      (-4 * I.epsilon N / I.delta) * normalizer I N s * (factor N s).eval (I.z lam) := by
  rw [bezout.History.chartFactor_physical_eval, history_chartFactor]
  simp only [responseFactor, eval_mul, eval_C]
  ring

/-- The constructed physical queries are exactly the normalized stopped-parity basis. -/
theorem history_query_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) :
    ((history I N hN).query s).eval lam = (psi N s).eval (I.z lam) / normalizer I N s := by
  rw [← bezout.History.chartQuery_physical_eval, history_chartQuery]
  simp only [eval_mul, eval_C, one_div_mul_eq_div]

/-- The sharp physical response bound for call s. -/
def responseBound (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  (4 * I.epsilon N / I.delta) * normalizer I N s * classMass N s

/-- The sharp physical query bound for call s. -/
def queryBound (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  1 / normalizer I N s

/-- Each physical response bound is positive. -/
theorem responseBound_pos (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s < N) : 0 < responseBound I N s := by
  have he := one_div_pos.mpr (I.den_pos N)
  have hd := I.delta_pos
  have hz := normalizer_pos I hN hs
  have hm := classMass_pos (s := s) hN
  unfold responseBound
  positivity

/-- Each physical query bound is positive. -/
theorem queryBound_pos (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s < N) : 0 < queryBound I N s :=
  one_div_pos.mpr (normalizer_pos I hN hs)

/-- Uniform scalar response bound over the whole physical spectral interval. -/
theorem response_bound (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) {lam : ℝ} (hlam : lam ∈ Set.Icc I.mu I.L) :
    |((history I N hN).response s).eval lam| ≤ responseBound I N s := by
  rw [history_response_eval, abs_mul, abs_mul]
  have he : 0 < 4 * I.epsilon N / I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  have hz := normalizer_pos I hN s.isLt
  have hf := factor_bound hN s.isLt (abs_le.mpr (I.z_mem hlam))
  rw [factor_eval_one hN s.isLt] at hf
  have ha : |-4 * I.epsilon N / I.delta| = 4 * I.epsilon N / I.delta := by
    rw [show -4 * I.epsilon N / I.delta = -(4 * I.epsilon N / I.delta) by ring,
      abs_neg, abs_of_pos he]
  rw [ha, abs_of_pos hz]
  exact mul_le_mul_of_nonneg_left hf (mul_pos he hz).le

/-- Uniform scalar query bound over the whole physical spectral interval. -/
theorem query_bound_physical (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) {lam : ℝ} (hlam : lam ∈ Set.Icc I.mu I.L) :
    |((history I N hN).query s).eval lam| ≤ queryBound I N s := by
  rw [history_query_eval, abs_div, abs_of_pos (normalizer_pos I hN s.isLt)]
  exact div_le_div_of_nonneg_right (abs_psi_eval_le_one hN s.isLt (abs_le.mpr (I.z_mem hlam)))
    (normalizer_pos I hN s.isLt).le

/-- The common physical endpoint attains the signed response bound. -/
theorem response_endpoint (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : ((history I N hN).response s).eval I.mu = -responseBound I N s := by
  rw [history_response_eval, I.z_mu, factor_eval_one hN s.isLt]
  unfold responseBound
  ring

/-- The same physical endpoint attains every query bound. -/
theorem query_endpoint_physical (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : ((history I N hN).query s).eval I.mu = queryBound I N s := by
  rw [history_query_eval, I.z_mu, psi_eval_one]
  rfl

/-- The exact product bound cancels the normalizer at every call. -/
theorem bound_product (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s < N) :
    responseBound I N s * queryBound I N s = 4 * I.epsilon N / I.delta * classMass N s := by
  unfold responseBound queryBound
  have hz := ne_of_gt (normalizer_pos I hN hs)
  field_simp

/-- The exact uniform spectral product energy is the squared sharp linear optimum. -/
theorem bound_energy (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (∑ s : Fin N, (responseBound I N s * queryBound I N s) ^ 2) = Lower.linearGain I N ^ 2 := by
  calc
    _ = ∑ s : Fin N, (4 * I.epsilon N / I.delta * classMass N s) ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [bound_product I hN s.isLt]
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => (4 * I.epsilon N / I.delta * classMass N s) ^ 2) N]
      exact scaled_classMass_energy I hN

/-- The actual physical endpoint realizes the full product energy. -/
theorem endpoint_energy (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    Lower.physicalKernelSq (history I N hN) I.mu I.mu = Lower.linearGain I N ^ 2 := by
  unfold Lower.physicalKernelSq Lower.physicalKernel
  simp only [response_endpoint, query_endpoint_physical, neg_mul, neg_sq]
  exact bound_energy I N hN

end
end bezout.Balanced
