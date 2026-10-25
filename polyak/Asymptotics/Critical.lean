import polyak.Regularity.Critical
import polyak.Asymptotics.Taylor
import polyak.Spectral.Optimal

/-!
Article: Appendix C, equation (criticalexp) for the actual heavy-ball rate.
Use: retain the ordinary two-sided derivative and O((κ−κc)²), with the exact coefficient.
-/

namespace polyak.Asymptotics
noncomputable section
open Filter Regularity Dynamics
open scoped Topology

/-- Article: the condition-number function is the original algorithm's actual exact rate. -/
theorem conditionRate_eq_originalRate {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    conditionRate (L/μ)=rate μ L (polyakAlpha μ L) (polyakBeta μ L) := by
  rw [Spectral.originalRate_eq_exp_T hμ hL,polyakQ_eq_conditionQ hμ hL]
  rfl

/-- Article: the actual rate equals one exactly at the critical condition number. -/
theorem conditionRate_critical : conditionRate Threshold.criticalKappa=1 := by
  have hqcrit : conditionQ Threshold.criticalKappa=Threshold.criticalQ :=
    (Threshold.conditionQ_eq_critical_iff Threshold.one_lt_criticalKappa).mpr rfl
  rw [conditionRate,hqcrit,
    (Spectral.T_eq_zero_iff Threshold.criticalQ_pos Threshold.criticalQ_lt_one).mpr rfl,
    Real.exp_zero]

/-- Article: the complete printed threshold expansion, with a genuine quadratic remainder. -/
theorem conditionRate_critical_expansion :
    (fun κ : ℝ => conditionRate κ-1-(κ-Threshold.criticalKappa)/(4*Threshold.criticalKappa))
      =O[𝓝 Threshold.criticalKappa] (fun κ => (κ-Threshold.criticalKappa)^2) := by
  simpa only [conditionRate_critical,div_eq_mul_inv,mul_comm,one_mul] using
    analytic_first_order conditionRate_analyticAt_critical conditionRate_hasDerivAt_critical

/-- Article: the ordinary two-sided derivative of the original rate at the threshold. -/
theorem conditionRate_critical_derivative :
    deriv conditionRate Threshold.criticalKappa=1/(4*Threshold.criticalKappa) :=
  conditionRate_hasDerivAt_critical.deriv

end
end polyak.Asymptotics
