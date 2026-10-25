import polyak.Boundary.P1.Gap
import polyak.Boundary.Tail

/-!
Article: Appendix B, the analytic one-atom tail m≥13.
Use: the cubic minimizer reserve and z≤3/4 dominate every later oscillation.
There is no lag cutoff assumption in this infinite-tail argument.
-/
noncomputable section
namespace polyak.Boundary.P1

theorem pow_cosh_le_cosh_nat_mul (t : ℝ) (n : ℕ) :
    Real.cosh t^n≤Real.cosh ((n : ℝ)*t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : ((n+1 : ℕ) : ℝ)*t=(n : ℝ)*t+t := by push_cast; ring
    rw [he,Real.cosh_add,pow_succ]
    have hs : 0≤Real.sinh ((n : ℝ)*t)*Real.sinh t := by
      rcases le_total 0 t with ht | ht
      · exact mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg n) ht))
          (Real.sinh_nonneg_iff.mpr ht)
      · exact mul_nonneg_of_nonpos_of_nonpos
          (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ht))
          (Real.sinh_nonpos_iff.mpr ht)
    exact (mul_le_mul_of_nonneg_right ih (Real.cosh_pos t).le).trans (le_add_of_nonneg_right hs)

theorem tail_at_thirteen {z η budget t : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ht : Real.cosh t=1/z) (hη : z^3/4≤η) (hb : budget≤4)
    (n : ℕ) (hn : 13≤n) : budget<η*Real.cosh ((n : ℝ)*t) := by
  have hzunit : z≤1 := by linarith
  have hη0 : 0≤η := le_trans (by positivity) hη
  have hpow : z^n≤z^3*(3/4 : ℝ)^10 := by
    calc
      _≤z^13 := pow_le_pow_of_le_one hz.le hzunit hn
      _=z^3*z^10 := by ring
      _≤z^3*(3/4 : ℝ)^10 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hz.le hz1 10) (pow_nonneg hz.le 3)
  have hcosh : 1≤z^n*Real.cosh ((n : ℝ)*t) := by
    have he : z^n*(1/z)^n=1 := by rw [← mul_pow]; simp [hz.ne']
    rw [← he]
    exact mul_le_mul_of_nonneg_left (by simpa only [ht] using pow_cosh_le_cosh_nat_mul t n)
      (pow_nonneg hz.le n)
  have hfour : 4<η*Real.cosh ((n : ℝ)*t) := by
    by_contra hnot
    have hupper := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (pow_nonneg hz.le n)
    have hlower := mul_le_mul_of_nonneg_left hcosh hη0
    have hchain : z^3/4≤4*(z^3*(3/4 : ℝ)^10) := by
      calc
        _≤η := hη
        _≤η*(z^n*Real.cosh ((n : ℝ)*t)) := by simpa using hlower
        _≤4*z^n := by nlinarith [hupper]
        _≤4*(z^3*(3/4 : ℝ)^10) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    norm_num at hchain
    nlinarith [pow_pos hz 3]
  exact hb.trans_lt hfour

end polyak.Boundary.P1
