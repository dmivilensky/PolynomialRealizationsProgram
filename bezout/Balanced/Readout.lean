import bezout.Balanced.Bounds

/-!
Article: bezout, Algorithm 2 reverse parity sums and Equation `eq:stopped-readout`.
Use: computes the actual output weights from two scalar accumulators, without
forming a factorization matrix or storing the vector history.
Proof: the second-kind parity difference and the exact response at zero Hessian.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The article's endpoint-aware first-kind Chebyshev weight. -/
def endpointWeight (r : ℕ) : ℝ := if r = 0 then 1 else 2

/-- First reverse scalar accumulator, zero beyond the last physical call. -/
def reverseP (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  if s < N then (U ℝ ((N - 1 - s : ℕ) : ℤ)).eval I.eta else 0

/-- Second reverse scalar accumulator, the exact parity Hall tail at eta. -/
def reverseQ (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ := (tail N s).eval I.eta

/-- The first reverse accumulator terminates at zero separately in each parity. -/
theorem reverseP_terminal (I : chebyshev1.SpectralInterval) {N s : ℕ} (hs : N ≤ s) :
    reverseP I N s = 0 := by simp [reverseP, show ¬s < N by omega]

/-- The second reverse accumulator has the same exact terminal convention. -/
theorem reverseQ_terminal (I : chebyshev1.SpectralInterval) {N s : ℕ} (hs : N ≤ s) :
    reverseQ I N s = 0 := by rw [reverseQ, tail_eq_zero hs, eval_zero]

/-- First reverse parity update in the printed scalar preparation. -/
theorem reverseP_step (I : chebyshev1.SpectralInterval) {N s : ℕ} (hs : s < N) :
    reverseP I N s = reverseP I N (s + 2) +
      endpointWeight (N - 1 - s) * (T ℝ ((N - 1 - s : ℕ) : ℤ)).eval I.eta := by
  by_cases ht : s + 2 < N
  · have hr : N - 1 - s = (N - 1 - (s + 2)) + 2 := by omega
    have h := congrArg (fun p : ℝ[X] => p.eval I.eta)
      (U_eq_two_mul_T_add_U ℝ ((N - 1 - (s + 2) : ℕ) : ℤ))
    simp only [eval_add, eval_mul, eval_ofNat] at h
    simp only [reverseP, hs, ht, ite_true, endpointWeight, show N - 1 - s ≠ 0 by omega, ite_false]
    rw [hr]
    push_cast
    linear_combination h
  · rw [reverseP_terminal I (s := s + 2) (by omega)]
    have hr : N - 1 - s = 0 ∨ N - 1 - s = 1 := by omega
    rcases hr with hr | hr <;> simp [reverseP, hs, hr, endpointWeight]

/-- Twice the Hall half-weight is the article's e_s coefficient. -/
theorem endpointWeight_eq_hallWeight (s : ℕ) : endpointWeight s / 2 = hallWeight s := by
  by_cases hs : s = 0 <;> simp [endpointWeight, hallWeight, hs]

/-- Second reverse parity update in the printed scalar preparation. -/
theorem reverseQ_step (I : chebyshev1.SpectralInterval) {N s : ℕ} (hs : s < N) :
    reverseQ I N s = reverseQ I N (s + 2) + endpointWeight s * reverseP I N s / 2 := by
  have h := congrArg (fun p : ℝ[X] => p.eval I.eta) (tail_sub_add_two hs)
  simp only [eval_sub, originalFactor, eval_mul, eval_C] at h
  simp only [reverseQ, reverseP, hs, ite_true]
  rw [show endpointWeight s * (U ℝ ((N - 1 - s : ℕ) : ℤ)).eval I.eta / 2 =
      hallWeight s * (U ℝ ((N - 1 - s : ℕ) : ℤ)).eval I.eta by
    rw [← endpointWeight_eq_hallWeight]; ring]
  linarith

/-- A physical additive response evaluated at zero is minus its actual output weight. -/
theorem response_zero {N : ℕ} (h : bezout.History N) (s : Fin N) : (h.response s).eval 0 = -h.b s := by
  have hr := congrArg (fun p : ℝ[X] => p.eval 0) (h.response_recurrence s)
  simpa only [eval_sub, eval_neg, eval_C, eval_mul, eval_X, zero_mul, sub_zero] using hr

/-- Exact actual readout weights computed by the two reverse scalar accumulators. -/
theorem history_readout (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (history I N hN).b s =
      4 * I.epsilon N * normalizer I N s / I.delta *
        (reverseQ I N s / omega N s - reverseQ I N (s + 2) / omega N (s + 2)) := by
  have hr := history_response_eval I N hN s 0
  have hz : I.z 0 = I.eta := by rw [I.z_eq]; ring
  rw [response_zero, hz] at hr
  simp only [factor, eval_sub, eval_mul, eval_C, one_div_mul_eq_div] at hr
  unfold reverseQ
  linear_combination -hr

end
end bezout.Balanced
