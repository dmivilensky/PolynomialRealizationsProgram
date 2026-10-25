import polyak.Regularity.OuterArcs
import polyak.Regularity.Inverse
import polyak.Boundary.P5.Derivative
import polyak.Boundary.SwitchIdentification

/-!
Article: Theorems classification and regularity, the global actual inverse.
Use: the complete central and outer source arcs discharge every derivative
input. The conclusions have no assumed continuity, source root or slope bound.
-/
noncomputable section
namespace polyak.Regularity
open Spectral Boundary Set

theorem V_regular_central {t : ℝ} (hG : Real.cosh t<P2.Ga) :
    AnalyticAt ℝ V t ∧ |deriv V t|<1 := by
  by_cases ht : t=0
  · subst t
    refine ⟨P5.V_analyticAt_zero,?_⟩
    rw [V_hasDerivAt_zero.deriv]
    norm_num
  · have hl : 1<Real.cosh t := Real.one_lt_cosh.mpr ht
    exact ⟨P5.V_analyticAt hl hG,P5.abs_deriv_V_lt_one hl hG⟩

theorem logarithmicCoordinate_strictMono : StrictMono logarithmicCoordinate := by
  apply logarithmicCoordinate_strictMono_of_central
  intro t ht
  have hh := V_regular_central ht
  exact ⟨hh.1.differentiableAt,hh.2⟩

theorem scalar_prescription {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∃! t : ℝ,t-V t=Real.log q :=
  scalar_prescription_unique hq hq1 logarithmicCoordinate_strictMono

theorem T_continuousAt {q : ℝ} (hq : 0<q) (hq1 : q<1) : ContinuousAt T q :=
  T_continuousAt_of_coordinate_strictMono hq hq1 logarithmicCoordinate_strictMono

theorem T_continuousOn : ContinuousOn T (Ioo (0 : ℝ) 1) :=
  fun _ hq => (T_continuousAt hq.1 hq.2).continuousWithinAt

theorem conditionRate_continuousOn : ContinuousOn conditionRate (Ioi (1 : ℝ)) := by
  intro κ hκ
  have hq := Threshold.conditionQ_mem hκ
  have hQ : ContinuousAt Dynamics.conditionQ κ := by
    unfold Dynamics.conditionQ
    fun_prop (disch := positivity)
  exact (Real.continuous_exp.continuousAt.comp ((T_continuousAt hq.1 hq.2).comp hQ)).continuousWithinAt

theorem V_regular_off_switches {t : ℝ} (ha : Real.cosh t≠P2.Ga)
    (h₁ : Real.cosh t≠G1) (hW : Real.cosh t≠GW) :
    AnalyticAt ℝ V t ∧ |deriv V t|<1 := by
  by_cases hG : Real.cosh t<P2.Ga
  · exact V_regular_central hG
  · exact V_analytic_and_slope_outside_central
      (lt_of_le_of_ne (le_of_not_gt hG) ha.symm) h₁ hW

theorem conditionRate_analyticAt_off_switches {κ : ℝ} (hκ : 1<κ)
    (hne : ∀ i : Fin 5,κ≠switchingKappa i) : AnalyticAt ℝ conditionRate κ := by
  have hs := no_cosh_switch_of_no_kappa_switch hκ logarithmicCoordinate_strictMono hne
  have hh := V_regular_off_switches hs.1 hs.2.1 hs.2.2
  exact conditionRate_analyticAt_of_boundary hκ hh.1 (ne_of_lt (abs_lt.mp hh.2).2)

theorem switchingKappa_order : StrictMono switchingKappa :=
  switchingKappa_strictMono logarithmicCoordinate_strictMono

theorem switchingKappa_above_one (i : Fin 5) : 1<switchingKappa i :=
  one_lt_switchingKappa logarithmicCoordinate_strictMono i

theorem switchingKappa_brackets_critical :
    switchingKappa 2<Threshold.criticalKappa ∧ Threshold.criticalKappa<switchingKappa 3 :=
  switchingKappa_critical_bracket logarithmicCoordinate_strictMono

theorem T_at_switchingKappa (i : Fin 5) :
    T (Dynamics.conditionQ (switchingKappa i))=switchingExponent i :=
  T_conditionQ_switchingKappa logarithmicCoordinate_strictMono i

end polyak.Regularity
