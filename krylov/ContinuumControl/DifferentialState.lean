import krylov.ContinuumControl.SmoothIdentity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: main_krylov, apC:eq:state, continuous-density specialization.
Use: turn the proved physical differential equations into the genuine
integral state equations against the mass measure v² dx. This connects a
local feedback ODE solution to a continuous-density string state.
Source: mathlib's fundamental theorem of calculus and with-density integration.
-/

namespace krylov.ContinuumControl
noncomputable section
open Set MeasureTheory

/-- Post-origin continuous mass associated with a physical density v.
The distinguished initial unit atom is accounted for by the initial state.
Article: main_krylov, apC:eq:state. -/
def densityMass (v : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (v x ^ 2))

/-- Integrating a state coordinate against actual continuous mass gives
the expected weighted Lebesgue integral, with the precise half-open endpoints.
Article: main_krylov, apC:eq:state. -/
theorem integral_densityMass (v f : ℝ → ℝ) {a b : ℝ} (hv : Measurable v) (hab : a ≤ b) :
    (∫ x in Ioc a b, f x ∂densityMass v) = ∫ x in a..b, f x * v x ^ 2 := by
  unfold densityMass
  have hw : Measurable (fun x => ENNReal.ofReal (v x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hv.pow_const 2)
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f measurableSet_Ioc,
    intervalIntegral.integral_of_le hab]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm]

/-- The genuine integral equations follow from the physical ODE and
continuity of the chosen density. Integrability is proved from compactness.
Article: main_krylov, apC:eq:state. -/
theorem smooth_state_integral_equations {a b : ℝ} {φ p K v : ℝ → ℝ}
    (hstate : ∀ x ∈ uIcc a b, SmoothStringAt φ p K v x)
    (hv : ContinuousOn v (uIcc a b)) :
    φ b = φ a + (∫ x in a..b, p x) ∧
      p b = p a + (∫ x in a..b, φ x * v x ^ 2) ∧
      K b = K a + (∫ x in a..b, φ x ^ 2 * v x ^ 2) := by
  have hφc : ContinuousOn φ (uIcc a b) := fun x hx =>
    (hstate x hx).φ_deriv.continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (uIcc a b) := fun x hx =>
    (hstate x hx).p_deriv.continuousAt.continuousWithinAt
  have hφ := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => (hstate x hx).φ_deriv) hpc.intervalIntegrable
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => (hstate x hx).p_deriv) ((hφc.mul (hv.pow 2)).intervalIntegrable)
  have hK := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => (hstate x hx).K_deriv) (((hφc.pow 2).mul (hv.pow 2)).intervalIntegrable)
  constructor
  · linarith
  constructor <;> linarith

/-- Physical ODE solutions satisfy the source's integral state equations
against an actual measure, rather than only formal density-weighted rates.
Article: main_krylov, apC:eq:state. -/
theorem smooth_state_measure_integral_equations {a b : ℝ} {φ p K v : ℝ → ℝ}
    (hab : a ≤ b) (hstate : ∀ x ∈ uIcc a b, SmoothStringAt φ p K v x)
    (hv : ContinuousOn v (uIcc a b)) (hvm : Measurable v) :
    φ b = φ a + (∫ x in a..b, p x) ∧
      p b = p a + (∫ x in Ioc a b, φ x ∂densityMass v) ∧
      K b = K a + (∫ x in Ioc a b, φ x ^ 2 ∂densityMass v) := by
  rw [integral_densityMass v φ hvm hab,
    integral_densityMass v (fun x => φ x ^ 2) hvm hab]
  exact smooth_state_integral_equations hstate hv

end
end krylov.ContinuumControl
