import bezout.Lower.FourCorners
import bezout.Synthesis.Chebyshev
import chebyshev1.Chebyshev.EndpointDerivatives

/-!
Article: bezout, Theorem 2.1, Lemma C.2 and the odd-horizon part of
Theorem 4.1.
Use: transfers the sign-unrestricted four-corner inequality from endpoint
arrays to actual Chebyshev-exact causal histories. All normalization factors
refer to the physical oracle responses defined by the history execution.
-/

namespace bezout.Lower

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The diagonal corner at one is the endpoint derivative divided by two. -/
theorem chebyshevBezout_one_one (N : ℕ) :
    chebyshevBezout N 1 1 = (N : ℝ) ^ 2 / 2 := by
  simp [chebyshevBezout, History.dividedDifference, derivative_T_eval_one]

/-- Odd Chebyshev polynomials have the same derivative at both endpoints. -/
theorem chebyshev_derivative_neg_one (N : ℕ) (hodd : Odd N) :
    (T ℝ N).derivative.eval (-1) = (N : ℝ) ^ 2 := by
  have he : Even ((N : ℤ) - 1) := by
    obtain ⟨k, hk⟩ := hodd.exists_bit1
    refine ⟨(k : ℤ), ?_⟩
    omega
  rw [T_derivative_eq_U]
  simp only [eval_mul, eval_intCast, U_eval_neg_one,
    Int.negOnePow_even _ he]
  push_cast
  ring

/-- The second diagonal corner has the same positive mass at odd horizons. -/
theorem chebyshevBezout_neg_one_neg_one (N : ℕ) (hodd : Odd N) :
    chebyshevBezout N (-1) (-1) = (N : ℝ) ^ 2 / 2 := by
  simp [chebyshevBezout, History.dividedDifference, chebyshev_derivative_neg_one N hodd]

/-- The two off-diagonal corners carry the smaller, horizon-independent mass. -/
theorem chebyshevBezout_one_neg_one (N : ℕ) (hodd : Odd N) :
    chebyshevBezout N 1 (-1) = 1 / 2 := by
  have ho : Odd (N : ℤ) := by exact_mod_cast hodd
  norm_num [chebyshevBezout, History.dividedDifference,
    Int.negOnePow_odd _ ho]

/-- The reversed off-diagonal corner has the same value. -/
theorem chebyshevBezout_neg_one_one (N : ℕ) (hodd : Odd N) :
    chebyshevBezout N (-1) 1 = 1 / 2 := by
  have ho : Odd (N : ℤ) := by exact_mod_cast hodd
  norm_num [chebyshevBezout, History.dividedDifference,
    Int.negOnePow_odd _ ho]

/-- Lemma C.2 for every real separated Chebyshev factorization. Its
hypotheses impose no degree, sign, or normalization restrictions. -/
theorem chebyshev_symmetric_four_corner_lower (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (f q : Fin N → ℝ → ℝ)
    (hf : ∀ x y, (∑ s, f s x * q s y) = chebyshevBezout N x y) :
    oddEnergy N ≤ symmetricCornerEnergy
      (fun s => f s 1) (fun s => f s (-1)) (fun s => q s 1) (fun s => q s (-1)) := by
  apply symmetric_four_corner_lower N hN hodd (Fintype.card_fin N)
  · rw [hf, chebyshevBezout_one_one]
  · rw [hf, chebyshevBezout_one_neg_one N hodd]
  · rw [hf, chebyshevBezout_neg_one_one N hodd]
  · rw [hf, chebyshevBezout_neg_one_neg_one N hodd]

/-- The ordinary form of the same factorization bound. -/
theorem chebyshev_four_corner_lower (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (f q : Fin N → ℝ → ℝ)
    (hf : ∀ x y, (∑ s, f s x * q s y) = chebyshevBezout N x y) :
    oddEnergy N ≤ fourCornerEnergy
      (fun s => f s 1) (fun s => f s (-1)) (fun s => q s 1) (fun s => q s (-1)) :=
  (chebyshev_symmetric_four_corner_lower N hN hodd f q hf).trans
    (symmetricCornerEnergy_le_fourCornerEnergy _ _ _ _)

/-- The actual normalized factors of every Chebyshev-exact history satisfy
the stronger symmetric four-corner inequality. -/
theorem history_chart_symmetric_four_corner_lower {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I)
    (hN : 3 ≤ N) (hodd : Odd N) :
    oddEnergy N ≤ symmetricCornerEnergy
      (fun s => (h.chartFactor I s).eval 1) (fun s => (h.chartFactor I s).eval (-1))
      (fun s => (h.chartQuery I s).eval 1) (fun s => (h.chartQuery I s).eval (-1)) := by
  exact chebyshev_symmetric_four_corner_lower N hN hodd
    (fun s x => (h.chartFactor I s).eval x) (fun s x => (h.chartQuery I s).eval x)
    (h.chart_factorization I he)

/-- The ordinary four-corner inequality also holds for every actual history. -/
theorem history_chart_four_corner_lower {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I)
    (hN : 3 ≤ N) (hodd : Odd N) :
    oddEnergy N ≤ fourCornerEnergy
      (fun s => (h.chartFactor I s).eval 1) (fun s => (h.chartFactor I s).eval (-1))
      (fun s => (h.chartQuery I s).eval 1) (fun s => (h.chartQuery I s).eval (-1)) :=
  (history_chart_symmetric_four_corner_lower h I he hN hodd).trans
    (symmetricCornerEnergy_le_fourCornerEnergy _ _ _ _)

end
end bezout.Lower
