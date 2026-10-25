import polyak.Regularity.Global
import polyak.Asymptotics.Critical
import polyak.Asymptotics.SmallQActual
import polyak.Asymptotics.ActualLimit

/-!
Article: Theorem regularity, including both asymptotic ends and the critical expansion.
Use: conditionRate is the original algorithmic rate by
Asymptotics.conditionRate_eq_originalRate; no proposed algebraic rate is substituted.
-/
noncomputable section
namespace polyak.Results
open Regularity Boundary _root_.polyak.Asymptotics Filter Set
open scoped Topology

theorem regularity :
    ContinuousOn conditionRate (Ioi (1 : ℝ)) ∧
    StrictMonoOn conditionRate (Ioi (1 : ℝ)) ∧
    (∀ κ : ℝ,1<κ → (∀ i : Fin 5,κ≠switchingKappa i) → AnalyticAt ℝ conditionRate κ) ∧
    AnalyticAt ℝ conditionRate Threshold.criticalKappa ∧
    ((fun κ : ℝ => conditionRate κ-1-(κ-Threshold.criticalKappa)/(4*Threshold.criticalKappa))
      =O[𝓝 Threshold.criticalKappa] (fun κ => (κ-Threshold.criticalKappa)^2)) ∧
    ((fun q => SmallQ.actualFactor q-
        ((1+Real.sqrt 2)*q-(2+3*Real.sqrt 2/2)*q^2))
      =O[𝓝[>] (0 : ℝ)] (fun q => q^3)) ∧
    ((fun q => SmallQ.actualFactor q-Spiral.factor q-((10+7*Real.sqrt 2)/4)*q^3)
      =O[𝓝[>] (0 : ℝ)] (fun q => q^4)) ∧
    Tendsto conditionRate (atTop : Filter ℝ) (𝓝 limitingFactor) :=
  ⟨conditionRate_continuousOn,conditionRate_strictMonoOn,
    fun _ hκ hne => conditionRate_analyticAt_off_switches hκ hne,
    conditionRate_analyticAt_critical,conditionRate_critical_expansion,
    SmallQ.actualFactor_expansion,SmallQ.actual_spiral_excess_expansion,
    conditionRate_tendsto_atTop⟩

theorem switching_points_ordered :
    1<switchingKappa 0 ∧ switchingKappa 0<switchingKappa 1 ∧
    switchingKappa 1<switchingKappa 2 ∧ switchingKappa 2<switchingKappa 3 ∧
    switchingKappa 3<switchingKappa 4 :=
  ⟨switchingKappa_above_one 0,switchingKappa_order (by decide),
    switchingKappa_order (by decide),switchingKappa_order (by decide),
    switchingKappa_order (by decide)⟩

end polyak.Results
