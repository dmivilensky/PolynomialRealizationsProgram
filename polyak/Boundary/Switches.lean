import polyak.Boundary.ScalarPrescription

/-!
Article: Theorem classification and the regime table, the five switches.
Use: the ordered exponent switches are mapped by the actual scalar coordinate;
the condition-number transformation preserves their strict order.
-/
noncomputable section
namespace polyak.Boundary
open Spectral Set

def switchingExponent : Fin 5 → ℝ :=
  ![-Real.arcosh GW,-Real.arcosh G1,-Real.arcosh P2.Ga,Real.arcosh P2.Ga,Real.arcosh G1]

def switchingQ (i : Fin 5) : ℝ := Real.exp (logarithmicCoordinate (switchingExponent i))

def conditionNumberOfQ (q : ℝ) : ℝ := ((1+q)/(1-q))^2

def switchingKappa (i : Fin 5) : ℝ := conditionNumberOfQ (switchingQ i)

theorem exp_neg_arsinh (u : ℝ) :
    Real.exp (-Real.arsinh u)=Real.sqrt (1+u^2)-u := by
  rw [←Real.arsinh_neg,Real.exp_arsinh,neg_sq]
  ring

theorem exp_neg_arcosh {G : ℝ} (hG : 1≤G) :
    Real.exp (-Real.arcosh G)=G-Real.sqrt (G^2-1) := by
  have he := Real.cosh_eq (Real.arcosh G)
  rw [Real.cosh_arcosh hG,Real.exp_arcosh hG] at he
  linarith

theorem q_minus_formula {G u : ℝ} (hG : 1≤G)
    (hV : V (-Real.arcosh G)=Real.arsinh u) :
    Real.exp (logarithmicCoordinate (-Real.arcosh G))=
      (G-Real.sqrt (G^2-1))*(Real.sqrt (1+u^2)-u) := by
  rw [logarithmicCoordinate,hV,sub_eq_add_neg,Real.exp_add,exp_neg_arcosh hG,exp_neg_arsinh]

theorem q_plus_formula {G u : ℝ} (hG : 1≤G)
    (hV : V (Real.arcosh G)=Real.arsinh u) :
    Real.exp (logarithmicCoordinate (Real.arcosh G))=
      (G+Real.sqrt (G^2-1))*(Real.sqrt (1+u^2)-u) := by
  rw [logarithmicCoordinate,hV,sub_eq_add_neg,Real.exp_add,Real.exp_arcosh hG,exp_neg_arsinh]

theorem switchingExponent_strictMono : StrictMono switchingExponent := by
  have ha : 1<P2.Ga := by linarith [P2.Ga_bounds.1]
  have hb : 1<G1 := by linarith [G1_bounds.1]
  have hc : 1<GW := by linarith [GW_bounds.1]
  have h₁ := (Real.arcosh_lt_arcosh (by linarith : (0 : ℝ)<P2.Ga)
    (by linarith : (0 : ℝ)<G1)).mpr P2.Ga_lt_G1
  have h₂ := (Real.arcosh_lt_arcosh (by linarith : (0 : ℝ)<G1)
    (by linarith : (0 : ℝ)<GW)).mpr G1_lt_GW
  have hp := Real.arcosh_pos ha
  intro i j hij
  have hv : i.val<j.val := hij
  fin_cases i <;> fin_cases j
  all_goals norm_num only [Fin.val_mk] at hv
  all_goals first | omega | (norm_num [switchingExponent]; linarith)

theorem logarithmicCoordinate_at_last_switch_neg :
    logarithmicCoordinate (switchingExponent 4)<0 := by
  let t := Real.arcosh G1
  have hg : 1<G1 := by linarith [G1_bounds.1]
  have hc : Real.cosh t=G1 := Real.cosh_arcosh hg.le
  have hu : 1/2<1-1/(2*G1) := by
    have hd : (0 : ℝ)<2*G1 := by positivity
    have hh : 1/(2*G1)<1/2 := (div_lt_iff₀ hd).mpr (by linarith)
    linarith
  have hs : Real.sinh t<1/2 := by
    have he := Real.cosh_sq_sub_sinh_sq t
    rw [hc] at he
    nlinarith [G1_bounds.2,Real.sinh_nonneg_iff.mpr (Real.arcosh_nonneg hg.le)]
  have hV : V t=Real.arsinh (1-1/(2*G1)) := by
    rw [spiral_optimal (by rw [hc]) (by rw [hc]; exact G1_lt_GW.le),hc]
  have htV : t<V t := by
    rw [hV]
    apply Real.sinh_lt_sinh.mp
    rw [Real.sinh_arsinh]
    exact hs.trans hu
  change t-V t<0
  linarith

theorem switchingQ_strictMono (hmono : StrictMono logarithmicCoordinate) :
    StrictMono switchingQ := Real.exp_strictMono.comp (hmono.comp switchingExponent_strictMono)

theorem switchingQ_mem (hmono : StrictMono logarithmicCoordinate) (i : Fin 5) :
    switchingQ i∈Ioo (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _,?_⟩
  have hlast : switchingQ 4<1 := by
    rw [switchingQ,Real.exp_lt_one_iff]
    exact logarithmicCoordinate_at_last_switch_neg
  exact ((switchingQ_strictMono hmono).monotone (show i≤4 by omega)).trans_lt hlast

theorem exp_logarithmicCoordinate_zero :
    Real.exp (logarithmicCoordinate 0)=Threshold.criticalQ := by
  have he : logarithmicCoordinate 0=Real.log Threshold.criticalQ := by
    unfold logarithmicCoordinate
    rw [Threshold.V_zero,Threshold.log_criticalQ]
    ring
  rw [he,Real.exp_log Threshold.criticalQ_pos]

theorem switchingQ_critical_bracket (hmono : StrictMono logarithmicCoordinate) :
    switchingQ 2<Threshold.criticalQ ∧ Threshold.criticalQ<switchingQ 3 := by
  have ha : 0<Real.arcosh P2.Ga := Real.arcosh_pos (by linarith [P2.Ga_bounds.1])
  rw [←exp_logarithmicCoordinate_zero]
  constructor
  · apply Real.exp_lt_exp.mpr (hmono _)
    change -Real.arcosh P2.Ga<0
    linarith
  · apply Real.exp_lt_exp.mpr (hmono _)
    exact ha

theorem conditionNumberOfQ_strictMonoOn : StrictMonoOn conditionNumberOfQ (Ioo 0 1) := by
  intro q hq r hr hqr
  have hdq : 0<1-q := by linarith [hq.2]
  have hdr : 0<1-r := by linarith [hr.2]
  have hfrac : (1+q)/(1-q)<(1+r)/(1-r) :=
    (div_lt_div_iff₀ hdq hdr).mpr (by nlinarith)
  have hpos : 0<(1+q)/(1-q) := div_pos (by linarith [hq.1]) hdq
  unfold conditionNumberOfQ
  nlinarith

theorem switchingKappa_strictMono (hmono : StrictMono logarithmicCoordinate) :
    StrictMono switchingKappa := by
  intro i j hij
  exact conditionNumberOfQ_strictMonoOn (switchingQ_mem hmono i)
    (switchingQ_mem hmono j) (switchingQ_strictMono hmono hij)

theorem one_lt_switchingKappa (hmono : StrictMono logarithmicCoordinate) (i : Fin 5) :
    1<switchingKappa i := by
  have hq := switchingQ_mem hmono i
  have hd : 0<1-switchingQ i := by linarith [hq.2]
  have hf : 1<(1+switchingQ i)/(1-switchingQ i) :=
    (lt_div_iff₀ hd).mpr (by linarith [hq.1])
  unfold switchingKappa conditionNumberOfQ
  nlinarith

theorem conditionQ_switchingKappa (hmono : StrictMono logarithmicCoordinate) (i : Fin 5) :
    Dynamics.conditionQ (switchingKappa i)=switchingQ i := by
  have hq := switchingQ_mem hmono i
  have hd : 1-switchingQ i≠0 := by linarith [hq.2]
  have hp : 0<(1+switchingQ i)/(1-switchingQ i) :=
    div_pos (by linarith [hq.1]) (by linarith [hq.2])
  unfold Dynamics.conditionQ switchingKappa conditionNumberOfQ
  rw [Real.sqrt_sq_eq_abs,abs_of_pos hp]
  field_simp
  ring

theorem T_switchingQ (hmono : StrictMono logarithmicCoordinate) (i : Fin 5) :
    T (switchingQ i)=switchingExponent i := by
  have hq := switchingQ_mem hmono i
  have hactual : logarithmicCoordinate (T (switchingQ i))=Real.log (switchingQ i) := by
    unfold logarithmicCoordinate
    linarith [Regularity.T_sub_log_eq_V hq.1 hq.2]
  rw [switchingQ,Real.log_exp] at hactual
  exact hmono.injective hactual

theorem T_conditionQ_switchingKappa (hmono : StrictMono logarithmicCoordinate) (i : Fin 5) :
    T (Dynamics.conditionQ (switchingKappa i))=switchingExponent i := by
  rw [conditionQ_switchingKappa hmono,T_switchingQ hmono]

theorem logarithmicCoordinate_positive_GW : 0<logarithmicCoordinate (Real.arcosh GW) := by
  have hg : 1<GW := by linarith [GW_bounds.1]
  let t := Real.arcosh GW
  have hc : Real.cosh t=GW := Real.cosh_arcosh hg.le
  have hu : 1-1/(2*GW)<3/4 := by
    have hd : (0 : ℝ)<2*GW := by positivity
    have hh : 1/4<1/(2*GW) := (lt_div_iff₀ hd).mpr (by linarith [GW_bounds.2])
    linarith
  have hs : 3/4<Real.sinh t := by
    have he := Real.cosh_sq_sub_sinh_sq t
    rw [hc] at he
    nlinarith [GW_bounds.1,Real.sinh_nonneg_iff.mpr (Real.arcosh_nonneg hg.le)]
  have hV : V t=Real.arsinh (1-1/(2*GW)) := by
    rw [spiral_optimal (by rw [hc]; exact G1_lt_GW.le) (by rw [hc]),hc]
  have htV : V t<t := by
    rw [hV]
    apply Real.sinh_lt_sinh.mp
    rw [Real.sinh_arsinh]
    exact hu.trans hs
  change 0<t-V t
  linarith

theorem switchingKappa_critical_bracket (hmono : StrictMono logarithmicCoordinate) :
    switchingKappa 2<Threshold.criticalKappa ∧ Threshold.criticalKappa<switchingKappa 3 := by
  have hq := switchingQ_critical_bracket hmono
  constructor
  · apply (Threshold.conditionQ_lt_critical_iff (one_lt_switchingKappa hmono 2)).mp
    rw [conditionQ_switchingKappa hmono]
    exact hq.1
  · apply (Threshold.critical_lt_conditionQ_iff (one_lt_switchingKappa hmono 3)).mp
    rw [conditionQ_switchingKappa hmono]
    exact hq.2

end polyak.Boundary
