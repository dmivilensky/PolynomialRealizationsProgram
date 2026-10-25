import polyak.Spectral.Interior
import polyak.Spiral.Feasibility
import polyak.Threshold.Results

/-!
Article: Theorem spectral, the attained actual exponent and its twist boundary.
Use: the noncritical optimal exponent gives a strictly positive twist on the
even boundary V(|T|); the only zero exponent is the exact golden-ratio threshold.
Proof: the explicitly feasible spiral gives the strict quadratic lower bound,
local persistence gives boundary equality, and the threshold bounds identify zero.
-/

namespace polyak.Spectral

noncomputable section

/-- Article: the actual optimal exponent strictly exceeds the quadratic exponent. -/
theorem log_lt_T {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : Real.log q < T q := by
  have hsp : Real.log (Spiral.factor q) ≤ T q :=
    (isGreatest_T hq).2 ⟨_, _, Spiral.actual_feasible hq hq1⟩
  exact (Spiral.log_q_lt_log_factor hq hq1).trans_le hsp

/-- Article: the optimal actual twist is strictly positive, including criticality. -/
theorem actual_twist_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    0 < T q - Real.log q := sub_pos.mpr (log_lt_T hq hq1)

/-- Article: the actual optimal twist lies on V at the absolute optimal exponent. -/
theorem actual_boundary_abs {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : T q ≠ 0) :
    T q - Real.log q = V |T q| := by
  rw [actual_boundary hq ht (actual_twist_pos hq hq1)]
  rcases le_total 0 (T q) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, V_even]

/-- Article: the normalized boundary twist is strictly positive away from criticality. -/
theorem sinh_V_abs_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (ht : T q ≠ 0) :
    0 < Real.sinh (V |T q|) := by
  rw [← actual_boundary_abs hq hq1 ht]
  simpa only [Real.sinh_zero] using Real.sinh_lt_sinh.mpr (actual_twist_pos hq hq1)

/-- Article: the actual optimal exponent vanishes exactly at the critical quadratic factor. -/
theorem T_eq_zero_iff {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    T q = 0 ↔ q = Threshold.criticalQ := by
  constructor
  · intro ht
    rcases lt_trichotomy q Threshold.criticalQ with hc | hc | hc
    · have hr := Threshold.polyakGrowthRate_lt_one hq hc
      change freeRate q < 1 at hr
      rw [freeRate_eq_exp_T hq, ht, Real.exp_zero] at hr
      exact (lt_irrefl _ hr).elim
    · exact hc
    · have hsp : Real.log (Spiral.factor q) ≤ T q :=
        (isGreatest_T hq).2 ⟨_, _, Spiral.actual_feasible hq hq1⟩
      have hp := Real.log_pos (Spiral.one_lt_factor hq hq1 hc)
      rw [ht] at hsp
      exact (not_lt_of_ge hsp hp).elim
  · rintro rfl
    have hu := Threshold.polyakGrowthRate_critical_le_one
    change freeRate Threshold.criticalQ ≤ 1 at hu
    rw [freeRate_eq_exp_T Threshold.criticalQ_pos, ← Real.exp_zero,
      Real.exp_le_exp] at hu
    have hl : Real.log (Spiral.factor Threshold.criticalQ) ≤ T Threshold.criticalQ :=
      (isGreatest_T Threshold.criticalQ_pos).2
        ⟨_, _, Spiral.actual_feasible Threshold.criticalQ_pos Threshold.criticalQ_lt_one⟩
    rw [Spiral.factor_critical, Real.log_one] at hl
    exact le_antisymm hu hl

end
end polyak.Spectral
