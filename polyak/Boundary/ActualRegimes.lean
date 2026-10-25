import polyak.Boundary.ActualSpiral
import polyak.Boundary.Classification.Results
import polyak.Regularity.Global

/-!
Article: Proposition spiralsub and the exact equality set in the rate figure.
Use: the actual scalar inverse turns the fixed-exponent classification into
the two closed condition-number intervals and the isolated critical point.
-/
noncomputable section
namespace polyak.Boundary
open Spectral Regularity Set

theorem actual_factor_spiral_iff_cosh {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    Real.exp (T q)=Spiral.factor q ↔
      (G1≤Real.cosh (T q) ∧ Real.cosh (T q)≤GW) ∨ T q=0 := by
  apply (actual_factor_eq_spiral_iff_boundary hq hq1).trans
  simpa only [Spiral.twist,Spiral.G] using Classification.spiral_optimal_iff (T q)

theorem spiral_strictly_suboptimal {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hG : GW<Real.cosh (Real.log (Spiral.factor q)) ∨
      (1<Real.cosh (Real.log (Spiral.factor q)) ∧ Real.cosh (Real.log (Spiral.factor q))<G1)) :
    Spiral.factor q<Real.exp (T q) := by
  apply spiral_lt_actual_of_boundary_improvement hq hq1
  change Real.arsinh (1-1/(2*Real.cosh (Real.log (Spiral.factor q))))<_
  rcases hG with ho|hi
  · exact Classification.strict_spiral_outer ho
  · exact Classification.strict_spiral_inner hi.1 hi.2

def conditionExponent (κ : ℝ) : ℝ := T (Dynamics.conditionQ κ)

theorem conditionExponent_strictMonoOn : StrictMonoOn conditionExponent (Ioi (1 : ℝ)) := by
  intro κ hκ r hr hκr
  exact T_strictMonoOn (Threshold.conditionQ_mem hκ) (Threshold.conditionQ_mem hr)
    (conditionQ_strictMonoOn hκ hr hκr)

theorem switch_le_iff_exponent_le {κ : ℝ} (hκ : 1<κ) (i : Fin 5) :
    switchingKappa i≤κ ↔ switchingExponent i≤conditionExponent κ := by
  have hi := switchingKappa_above_one i
  have he : conditionExponent (switchingKappa i)=switchingExponent i := T_at_switchingKappa i
  constructor
  · intro h
    rw [←he]
    exact conditionExponent_strictMonoOn.monotoneOn hi hκ h
  · intro h
    by_contra hn
    have hh := conditionExponent_strictMonoOn hκ hi (lt_of_not_ge hn)
    rw [he] at hh
    linarith

theorem le_switch_iff_exponent_le {κ : ℝ} (hκ : 1<κ) (i : Fin 5) :
    κ≤switchingKappa i ↔ conditionExponent κ≤switchingExponent i := by
  have hi := switchingKappa_above_one i
  have he : conditionExponent (switchingKappa i)=switchingExponent i := T_at_switchingKappa i
  constructor
  · intro h
    rw [←he]
    exact conditionExponent_strictMonoOn.monotoneOn hκ hi h
  · intro h
    by_contra hn
    have hh := conditionExponent_strictMonoOn hi hκ (lt_of_not_ge hn)
    rw [he] at hh
    linarith

theorem actual_exponent_lt_positive_GW {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    T q<Real.arcosh GW := by
  apply logarithmicCoordinate_strictMono.lt_iff_lt.mp
  have he : logarithmicCoordinate (T q)=Real.log q := by
    unfold logarithmicCoordinate
    linarith [T_sub_log_eq_V hq hq1]
  rw [he]
  exact (Real.log_neg hq hq1).trans logarithmicCoordinate_positive_GW

theorem actual_spiral_cosh_iff_exponents {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    (G1≤Real.cosh (T q) ∧ Real.cosh (T q)≤GW) ↔
      (-Real.arcosh GW≤T q ∧ T q≤ -Real.arcosh G1) ∨ Real.arcosh G1≤T q := by
  have hG1 : 1<G1 := by linarith [G1_bounds.1]
  have hGW : 1<GW := by linarith [GW_bounds.1]
  have hb : 0≤Real.arcosh G1 := Real.arcosh_nonneg hG1.le
  have hc : 0≤Real.arcosh GW := Real.arcosh_nonneg hGW.le
  have hlo : G1≤Real.cosh (T q) ↔ Real.arcosh G1≤|T q| := by
    rw [←Real.cosh_arcosh hG1.le,Real.cosh_le_cosh,abs_of_nonneg hb,Real.arcosh_cosh hb]
  have hhi : Real.cosh (T q)≤GW ↔ |T q|≤Real.arcosh GW := by
    rw [←Real.cosh_arcosh hGW.le,Real.cosh_le_cosh,abs_of_nonneg hc,Real.arcosh_cosh hc]
  rw [hlo,hhi]
  have htop := actual_exponent_lt_positive_GW hq hq1
  by_cases ht : 0≤T q
  · rw [abs_of_nonneg ht]
    constructor
    · intro h
      exact Or.inr h.1
    · intro h
      rcases h with h|h
      · exact ⟨by linarith [h.2],htop.le⟩
      · exact ⟨h,htop.le⟩
  · rw [abs_of_neg (lt_of_not_ge ht)]
    constructor
    · intro h
      exact Or.inl ⟨by linarith [h.2],by linarith [h.1]⟩
    · intro h
      rcases h with h|h
      · exact ⟨by linarith [h.2],by linarith [h.1]⟩
      · linarith

theorem conditionExponent_eq_zero_iff {κ : ℝ} (hκ : 1<κ) :
    conditionExponent κ=0 ↔ κ=Threshold.criticalKappa := by
  have hq := Threshold.conditionQ_mem hκ
  exact (T_eq_zero_iff hq.1 hq.2).trans (Threshold.conditionQ_eq_critical_iff hκ)

theorem conditionRate_eq_spiral_iff {κ : ℝ} (hκ : 1<κ) :
    conditionRate κ=Spiral.factor (Dynamics.conditionQ κ) ↔
      (switchingKappa 0≤κ ∧ κ≤switchingKappa 1) ∨
      κ=Threshold.criticalKappa ∨ switchingKappa 4≤κ := by
  have hq := Threshold.conditionQ_mem hκ
  rw [conditionRate,actual_factor_spiral_iff_cosh hq.1 hq.2,
    actual_spiral_cosh_iff_exponents hq.1 hq.2]
  change (((switchingExponent 0≤conditionExponent κ ∧ conditionExponent κ≤switchingExponent 1) ∨
    switchingExponent 4≤conditionExponent κ) ∨ conditionExponent κ=0) ↔ _
  rw [←switch_le_iff_exponent_le hκ 0,←le_switch_iff_exponent_le hκ 1,
    ←switch_le_iff_exponent_le hκ 4,conditionExponent_eq_zero_iff hκ]
  tauto

end polyak.Boundary
