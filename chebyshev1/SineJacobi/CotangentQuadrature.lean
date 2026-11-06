import chebyshev1.SineJacobi.CotangentRegularization
import chebyshev1.Analysis.MidpointQuadrature
import chebyshev1.SineJacobi.CotangentAsymptotics

/-! Uniform midpoint quadrature of the smooth part of the first Green diagonal. -/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set
open scoped BigOperators

theorem regularCotangent_midpoint_bound :
    ∃ M, 0 ≤ M ∧ ∀ N : ℕ, 0 < N →
      |(π / 2) * Analysis.midpointSum regularCotangent N - log (2 / π)| ≤
        M / (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbnd⟩ := regularCotangent_second_bound
  have hf (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt regularCotangent (deriv regularCotangent x) x := by
    have hx' : x ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact ((regularCotangent_contDiff.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt
      (by norm_num)).hasDerivAt
  have hf' (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (deriv regularCotangent) (deriv (deriv regularCotangent) x) x := by
    have hx' : x ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hd : ContDiffOn ℝ 1 (deriv regularCotangent) (Ioo (-2 : ℝ) 2) :=
      regularCotangent_contDiff.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ((hd.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)).hasDerivAt
  refine ⟨(π / 2) * C, mul_nonneg (by positivity) hC, fun N hN => ?_⟩
  have h := Analysis.midpointSum_error_bound hC hf hf' hbnd N hN
  rw [regularCotangent_integral] at h
  have he : (π / 2) * Analysis.midpointSum regularCotangent N - log (2 / π) =
      (π / 2) * (Analysis.midpointSum regularCotangent N - (2 / π) * log (2 / π)) := by
    field_simp [pi_ne_zero]
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < π / 2)]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

/-- Exact pole extraction from the finite first Green diagonal. -/
theorem first_green_regularized_sum (N : ℕ) (hN : 0 < N) :
    greenWeight N 0 = sinc (π / (2 * (N : ℝ))) *
      ((∑ s ∈ Finset.range N, 1 / ((s : ℝ) + 1 / 2)) +
        (π / 2) * Analysis.midpointSum regularCotangent N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [first_green_cotangent_sum N hN]
  have hterm (s : Fin N) :
      cot (nodeAngle N s / 2) =
        (2 * (N : ℝ) / π) * (1 / ((s : ℝ) + 1 / 2)) +
          regularCotangent (((s : ℝ) + 1 / 2) / N) := by
    have hx : ((s : ℝ) + 1 / 2) / N ∈ Ioo (0 : ℝ) 2 := by
      constructor
      · exact div_pos (by positivity) hn
      · apply (div_lt_iff₀ hn).mpr
        have hs' : (s : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_of_lt s.isLt)
        linarith
    rw [regularCotangent_eq _ hx]
    have ha : nodeAngle N s / 2 = π * (((s : ℝ) + 1 / 2) / N) / 2 := by
      dsimp [nodeAngle]; ring
    rw [ha]
    have hs0 : (s : ℝ) + 1 / 2 ≠ 0 := by positivity
    field_simp [pi_ne_zero, hn.ne', hs0]
    ring
  have hs : (∑ s : Fin N, cot (nodeAngle N s / 2)) =
      (2 * (N : ℝ) / π) * (∑ s : Fin N, 1 / ((s : ℝ) + 1 / 2)) +
        ∑ s : Fin N, regularCotangent (((s : ℝ) + 1 / 2) / N) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => hterm s)
  have hsum₁ := Fin.sum_univ_eq_sum_range (fun s : ℕ => 1 / ((s : ℝ) + 1 / 2)) N
  have hsum₂ := Fin.sum_univ_eq_sum_range
    (fun s : ℕ => regularCotangent (((s : ℝ) + 1 / 2) / N)) N
  rw [hs, hsum₁, hsum₂,
    sinc_of_ne_zero (div_ne_zero pi_ne_zero (mul_ne_zero (by norm_num) hn.ne'))]
  unfold Analysis.midpointSum
  field_simp [pi_ne_zero, hn.ne']

end
end chebyshev1.SineJacobi
