import chebyshev1.Chebyshev.Amplification
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! The exact maximum of the terminal residual on an expanded spectral interval. -/
namespace chebyshev1
noncomputable section
open Polynomial Polynomial.Chebyshev

private theorem eval_T_nonneg_bound (N : ℕ) {x M : ℝ}
    (hM : 1≤M) (hx : 0≤x) (hxM : x≤M) : |(T ℝ N).eval x| ≤ (T ℝ N).eval M := by
  by_cases hx1 : x≤1
  · exact (abs_eval_T_real_le_one N (abs_le.mpr ⟨by linarith,hx1⟩)).trans
      (one_le_eval_T_real N hM)
  · have hx1 : 1≤x := (lt_of_not_ge hx1).le
    rw [abs_of_nonneg ((one_le_eval_T_real N hx1).trans' (by norm_num : (0:ℝ)≤1)),
      ← Real.cosh_arcosh hx1,T_real_cosh,← Real.cosh_arcosh hM,T_real_cosh]
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hx1)),
      abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hM))]
    exact mul_le_mul_of_nonneg_left
      ((Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hxM) (by positivity)

theorem chebyshev_abs_le_expanded (N : ℕ) {x M : ℝ} (hM : 1≤M) (hx : |x|≤M) :
    |(T ℝ N).eval x| ≤ (T ℝ N).eval M := by
  by_cases hx0 : 0≤x
  · exact eval_T_nonneg_bound N hM hx0 ((le_abs_self x).trans hx)
  · have hh := eval_T_nonneg_bound N hM (by linarith : 0≤-x) ((neg_le_abs x).trans hx)
    simpa only [T_eval_neg,abs_mul,abs_unit_intCast,one_mul] using hh

namespace SpectralInterval

theorem expanded_residual_isGreatest (I : SpectralInterval) (N : ℕ) (delta : ℝ)
    (hd : 0≤delta) :
    IsGreatest {r : ℝ | ∃ lam ∈ Set.Icc (I.mu-delta) (I.L+delta),
      r=|(I.residual N).eval lam|}
      (I.epsilon N*(T ℝ N).eval (1+2*delta/I.delta)) := by
  have hM : 1≤1+2*delta/I.delta := by
    have hp := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hd) I.delta_pos.le
    linarith
  have hz : I.z (I.mu-delta)=1+2*delta/I.delta := by
    rw [I.z_eq]
    have hh := I.z_mu
    rw [I.z_eq] at hh
    rw [mul_sub]
    linear_combination hh
  constructor
  · refine ⟨I.mu-delta,⟨le_rfl,by linarith [I.mu_lt_L]⟩,?_⟩
    rw [I.residual_eval,hz,abs_div,abs_of_pos (I.den_pos N),
      abs_of_nonneg ((one_le_eval_T_real N hM).trans' (by norm_num : (0:ℝ)≤1))]
    simp [SpectralInterval.epsilon,div_eq_mul_inv,mul_comm]
  · rintro r ⟨lam,hlam,rfl⟩
    have hzx : |I.z lam|≤1+2*delta/I.delta := by
      rw [I.z_eq,abs_le]
      have hh0 := I.z_mu
      have hh1 : I.z I.L = -1 := by
        have hnum : I.L+I.mu-2*I.L = -I.delta := by
          dsimp [SpectralInterval.delta]
          ring
        change (I.L+I.mu-2*I.L)/I.delta = -1
        rw [hnum,neg_div,div_self I.delta_pos.ne']
      rw [I.z_eq] at hh0 hh1
      have hp : 0<2/I.delta := div_pos (by norm_num) I.delta_pos
      constructor
      · have hb := mul_le_mul_of_nonneg_left hlam.2 hp.le
        linear_combination hb - hh1
      · have hb := mul_le_mul_of_nonneg_left hlam.1 hp.le
        linear_combination hh0 + hb
    rw [I.residual_eval,abs_div,abs_of_pos (I.den_pos N)]
    have hb := div_le_div_of_nonneg_right (chebyshev_abs_le_expanded N hM hzx)
      (I.den_pos N).le
    simpa [SpectralInterval.epsilon,div_eq_mul_inv,mul_comm] using hb

end SpectralInterval
end
end chebyshev1
