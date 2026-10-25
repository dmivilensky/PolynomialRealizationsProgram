import polyak.Growth.SpectralUpper
import polyak.Waves.Polyak

/-!
Article: Theorem spectral, existence of T and the exact free growth rate.
Use: the actual Polyak multiplier connects independent spectral parameters to Γ.
Proof: the growth-exponent plateau supplies an attained feasible exponent, and
every feasible exponent is bounded by that same free growth rate.
-/

namespace polyak.Spectral
noncomputable section
open Set

/-- Article: the exponents on the actual Polyak tuning curve. -/
def exponents (q : ℝ) : Set ℝ := {t | ∃ ν C, Feasible (t-Real.log q) t ν C}

/-- Article: T(q). Use: the source supremum, proved to be an attained maximum below. -/
def T (q : ℝ) : ℝ := sSup (exponents q)

/-- Article: free growth for Polyak's normalized recurrence. -/
def freeRate (q : ℝ) : ℝ := Growth.growthRate 0 (2*q) (q^2)

/-- Article: actual spectral feasibility. Use: all original signs and the parameter C. -/
theorem actual_feasible_iff {q : ℝ} (hq : 0 < q) (t C : ℝ) (ν : Spectrum) :
    Waves.MixtureFeasible ν (Waves.multiplierMap 0 (2*q) (q^2) t) C t ↔
      Feasible (t-Real.log q) t ν C := by
  rw [Waves.multiplierMap_polyak q t hq, Waves.mixtureFeasible_polyak_iff]

/-- Article: positivity of the free Polyak rate. -/
theorem freeRate_pos (q : ℝ) : 0 < freeRate q := Growth.growthRate_pos _ _ _

/-- Article: every feasible exponent is bounded by free growth. -/
theorem feasible_exp_le_freeRate {q t C : ℝ} {ν : Spectrum} (hq : 0 < q)
    (h : Feasible (t-Real.log q) t ν C) : Real.exp t ≤ freeRate q := by
  exact Growth.exp_le_growthRate ν (by positivity : 2*q ≠ 0)
    ((actual_feasible_iff hq t C ν).mpr h)

/-- Article: an actual feasible exponent at the exact free rate. -/
theorem log_freeRate_mem_exponents {q : ℝ} (hq : 0 < q) :
    Real.log (freeRate q) ∈ exponents q := by
  obtain ⟨ν,C,h⟩ := Growth.exists_feasible_at_growth
    (A := 0) (β := q^2) (by positivity : 2*q ≠ 0)
  exact ⟨ν,C,(actual_feasible_iff hq _ C ν).mp h⟩

/-- Article: the maximal feasible exponent exists and is attained. -/
theorem isGreatest_log_freeRate {q : ℝ} (hq : 0 < q) :
    IsGreatest (exponents q) (Real.log (freeRate q)) := by
  refine ⟨log_freeRate_mem_exponents hq, ?_⟩
  rintro t ⟨ν,C,h⟩
  rw [← Real.exp_le_exp, Real.exp_log (freeRate_pos q)]
  exact feasible_exp_le_freeRate hq h

/-- Article: exact value of the source supremum. -/
theorem T_eq_log_freeRate {q : ℝ} (hq : 0 < q) : T q = Real.log (freeRate q) :=
  (isGreatest_log_freeRate hq).csSup_eq

/-- Article: maximum formulation of T(q). Use: retain the attained source definition. -/
theorem isGreatest_T {q : ℝ} (hq : 0 < q) : IsGreatest (exponents q) (T q) := by
  rw [T_eq_log_freeRate hq]
  exact isGreatest_log_freeRate hq

/-- Article: feasibility at the optimal exponent. -/
theorem T_mem {q : ℝ} (hq : 0 < q) :
    ∃ ν C, Feasible (T q-Real.log q) (T q) ν C := (isGreatest_T hq).1

/-- Article: the complete exact free-growth identity ρΓ=exp T. -/
theorem freeRate_eq_exp_T {q : ℝ} (hq : 0 < q) : freeRate q = Real.exp (T q) := by
  rw [T_eq_log_freeRate hq, Real.exp_log (freeRate_pos q)]

/-- Article: zero twist gives the quadratic exponent. -/
theorem log_mem_exponents {q : ℝ} (_hq : 0 < q) : Real.log q ∈ exponents q := by
  obtain ⟨ν,hν⟩ := feasible_zero (Real.log q)
  refine ⟨ν,0,?_⟩
  simpa only [sub_self] using hν

/-- Article: the maximal exponent is at least the quadratic exponent. -/
theorem log_le_T {q : ℝ} (hq : 0 < q) : Real.log q ≤ T q :=
  (isGreatest_T hq).2 (log_mem_exponents hq)

/-- Article: the a priori finite interval containing T. -/
theorem abs_T_sub_log_le {q : ℝ} (hq : 0 < q) :
    |T q-Real.log q| ≤ Real.arsinh 1 := by
  obtain ⟨ν,C,h⟩ := T_mem hq
  exact h.abs_v_le_arsinh_one

/-- Article: the original from-rest Polyak rate has the claimed upper bound. -/
theorem originalRate_le_exp_T {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) ≤
      Real.exp (T (Dynamics.polyakQ μ L)) := by
  have hh := Growth.originalRate_le_growthRate hμ hL (Dynamics.polyakAlpha_pos hμ hL)
    (Dynamics.polyakBeta_mem hμ hL).1
  rw [Dynamics.polyak_normalizedA hμ hL, Dynamics.polyak_normalizedB hμ hL] at hh
  change _ ≤ freeRate (Dynamics.polyakQ μ L) at hh
  rwa [freeRate_eq_exp_T (Dynamics.polyakQ_pos hμ hL)] at hh

end
end polyak.Spectral
