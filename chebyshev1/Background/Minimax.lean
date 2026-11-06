import chebyshev1.Chebyshev.Coordinates
import chebyshev1.Chebyshev.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-! The classical normalized Chebyshev minimax assertion used in the preliminaries. -/
namespace chebyshev1
noncomputable section
open Polynomial Polynomial.Chebyshev Set

/-- A polynomial normalized outside the interval cannot improve the Chebyshev bound. -/
theorem chebyshev_minimax_lower (eta : ℝ) (heta : 1 < eta) (N : ℕ)
    (p : ℝ[X]) (hp : p.natDegree ≤ N) (hnormal : p.eval eta = 1)
    (B : ℝ) (hB : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ B) :
    1 / (T ℝ N).eval eta ≤ B := by
  have hBnonneg : 0 ≤ B := (abs_nonneg (p.eval 0)).trans (hB 0 (by norm_num))
  have hBpos : 0 < B := by
    by_contra hh
    have hzero : B = 0 := le_antisymm (le_of_not_gt hh) hBnonneg
    have hpzero : p = 0 := by
      apply p.eq_of_infinite_eval_eq 0
      apply (Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono
      intro x hx
      simpa using (abs_nonpos_iff.mp (by simpa [hzero] using hB x hx))
    simp [hpzero] at hnormal
  let q : ℝ[X] := C B⁻¹ * p
  have hqdeg : q.degree ≤ (N : WithBot ℕ) := by
    exact (degree_le_natDegree).trans (by exact_mod_cast (natDegree_C_mul_le B⁻¹ p).trans hp)
  have hqbound : ∀ x ∈ Icc (-1 : ℝ) 1, |q.eval x| ≤ 1 := by
    intro x hx
    simp only [q, eval_mul, eval_C, abs_mul, abs_inv, abs_of_pos hBpos]
    exact (inv_mul_le_one₀ hBpos).mpr (hB x hx)
  have he := eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 0) heta.le hqdeg hqbound
  simp only [Function.iterate_zero, id_eq, q, eval_mul, eval_C, hnormal, mul_one] at he
  have hden : 0 < (T ℝ N).eval eta := zero_lt_one.trans_le (one_le_eval_T_real N heta.le)
  apply (div_le_iff₀ hden).mpr
  have hh := mul_le_mul_of_nonneg_left he hBpos.le
  simpa only [mul_inv_cancel₀ hBpos.ne'] using hh

/-- The normalized Chebyshev polynomial attains the lower bound. -/
theorem chebyshev_minimax_attained (eta : ℝ) (heta : 1 < eta) (N : ℕ) :
    let p : ℝ[X] := C ((T ℝ N).eval eta)⁻¹ * T ℝ N
    p.eval eta = 1 ∧ p.natDegree ≤ N ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1 / (T ℝ N).eval eta := by
  dsimp only
  have hd : 0 < (T ℝ N).eval eta := zero_lt_one.trans_le (one_le_eval_T_real N heta.le)
  refine ⟨by simp [hd.ne'], (natDegree_C_mul_le _ _).trans (by simp), ?_⟩
  intro x hx
  simp only [eval_mul, eval_C, abs_mul, abs_inv, abs_of_pos hd, one_div]
  exact mul_le_of_le_one_right (inv_nonneg.mpr hd.le) (abs_eval_T_real_le_one N (abs_le.mpr hx))

end
end chebyshev1
