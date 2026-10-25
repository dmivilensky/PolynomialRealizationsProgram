import polyak.Boundary.Switches

/-!
Article: Theorem regularity, identification of the five condition-number switches.
Use: the actual attained exponent satisfies the scalar equation. Its three
cosh cut values correspond to exactly five physical tunings in 0<q<1.
-/
noncomputable section
namespace polyak.Boundary
open Spectral Regularity Set

theorem exponent_eq_arcosh_or_neg {t G : ℝ} (hG : Real.cosh t=G) :
    t=Real.arcosh G ∨ t= -Real.arcosh G := by
  have habs : |t|=Real.arcosh G := by
    calc
      |t|=Real.arcosh (Real.cosh |t|) := (Real.arcosh_cosh (abs_nonneg t)).symm
      _=Real.arcosh G := by rw [Real.cosh_abs,hG]
  by_cases ht : 0≤t
  · exact Or.inl (by rwa [abs_of_nonneg ht] at habs)
  · apply Or.inr
    rw [abs_of_neg (lt_of_not_ge ht)] at habs
    linarith

theorem q_eq_exp_coordinate {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    q=Real.exp (logarithmicCoordinate (T q)) := by
  have he : logarithmicCoordinate (T q)=Real.log q := by
    unfold logarithmicCoordinate
    linarith [T_sub_log_eq_V hq hq1]
  rw [he,Real.exp_log hq]

theorem tuning_at_Ga {q : ℝ} (hq : 0<q) (hq1 : q<1) (hG : Real.cosh (T q)=P2.Ga) :
    q=switchingQ 2 ∨ q=switchingQ 3 := by
  have he := q_eq_exp_coordinate hq hq1
  rcases exponent_eq_arcosh_or_neg hG with hpos|hneg
  · right
    change q=Real.exp (logarithmicCoordinate (Real.arcosh P2.Ga))
    rwa [hpos] at he
  · left
    change q=Real.exp (logarithmicCoordinate (-Real.arcosh P2.Ga))
    rwa [hneg] at he

theorem tuning_at_G1 {q : ℝ} (hq : 0<q) (hq1 : q<1) (hG : Real.cosh (T q)=G1) :
    q=switchingQ 1 ∨ q=switchingQ 4 := by
  have he := q_eq_exp_coordinate hq hq1
  rcases exponent_eq_arcosh_or_neg hG with hpos|hneg
  · right
    change q=Real.exp (logarithmicCoordinate (Real.arcosh G1))
    rwa [hpos] at he
  · left
    change q=Real.exp (logarithmicCoordinate (-Real.arcosh G1))
    rwa [hneg] at he

theorem tuning_at_GW {q : ℝ} (hq : 0<q) (hq1 : q<1) (hG : Real.cosh (T q)=GW) :
    q=switchingQ 0 := by
  have he := q_eq_exp_coordinate hq hq1
  rcases exponent_eq_arcosh_or_neg hG with hpos|hneg
  · have hlog : logarithmicCoordinate (T q)=Real.log q := by
      unfold logarithmicCoordinate
      linarith [T_sub_log_eq_V hq hq1]
    rw [hpos] at hlog
    have hn := Real.log_neg hq hq1
    linarith [logarithmicCoordinate_positive_GW]
  · simpa only [hneg,switchingQ,switchingExponent,Matrix.cons_val_zero] using he

theorem no_cosh_switch_of_no_kappa_switch {κ : ℝ} (hκ : 1<κ)
    (hmono : StrictMono logarithmicCoordinate) (hne : ∀ i : Fin 5,κ≠switchingKappa i) :
    Real.cosh (T (Dynamics.conditionQ κ))≠P2.Ga ∧
    Real.cosh (T (Dynamics.conditionQ κ))≠G1 ∧
    Real.cosh (T (Dynamics.conditionQ κ))≠GW := by
  have hq := Threshold.conditionQ_mem hκ
  have hn (i : Fin 5) : Dynamics.conditionQ κ≠switchingQ i := by
    intro he
    apply hne i
    apply conditionQ_strictMonoOn.injOn hκ (one_lt_switchingKappa hmono i)
    rwa [conditionQ_switchingKappa hmono]
  refine ⟨?_,?_,?_⟩
  · intro hG
    rcases tuning_at_Ga hq.1 hq.2 hG with h|h
    · exact hn 2 h
    · exact hn 3 h
  · intro hG
    rcases tuning_at_G1 hq.1 hq.2 hG with h|h
    · exact hn 1 h
    · exact hn 4 h
  · intro hG
    exact hn 0 (tuning_at_GW hq.1 hq.2 hG)

end polyak.Boundary
