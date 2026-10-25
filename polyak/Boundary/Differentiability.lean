import polyak.Boundary.P1.SlopeJoin
import polyak.Boundary.P2.ClosedDerivative
import polyak.Boundary.Classification.Value
import polyak.Regularity.Critical

/-! The actual optimal boundary has an ordinary derivative everywhere,
including all regime switches, and its absolute value is strictly below one. -/
noncomputable section
namespace polyak.Boundary
open Spectral

/-- Ordinary differentiability and the strict derivative bound hold at every exponent. -/
theorem V_differentiable_and_derivative_bound (t : ℝ) :
    DifferentiableAt ℝ V t ∧ |deriv V t|<1 := by
  by_cases ht : t=0
  · subst t
    refine ⟨Regularity.V_hasDerivAt_zero.differentiableAt,?_⟩
    rw [Regularity.V_hasDerivAt_zero.deriv]
    norm_num
  have h1 : 1<Real.cosh t := Real.one_lt_cosh.mpr ht
  by_cases h5 : Real.cosh t≤P2.Ga
  · exact ⟨(P5.hasDerivAt_V_closed h1 h5).differentiableAt,P5.abs_deriv_V_lt_one_closed h1 h5⟩
  · by_cases h2 : Real.cosh t≤G1
    · have hp:=Classification.p2Parameter_spec ⟨(lt_of_not_ge h5).le,h2⟩
      exact ⟨(P2.hasDerivAt_V_closed hp.1 hp.2.symm).differentiableAt,
        P2.abs_deriv_V_lt_one_closed hp.1 hp.2.symm⟩
    · have hG1 : G1<Real.cosh t := lt_of_not_ge h2
      by_cases hW : Real.cosh t≤GW
      · rcases hW.eq_or_lt with he|hl
        · exact ⟨(P1.hasDerivAt_V_at_GW he).differentiableAt,P1.abs_deriv_V_at_GW_lt_one he⟩
        · exact ⟨(hasDerivAt_V_spiral hG1 hl).differentiableAt,abs_deriv_V_spiral_lt_one hG1 hl⟩
      · have hGW : GW<Real.cosh t := lt_of_not_ge hW
        have hz : 1/Real.cosh t∈Set.Ioo (0 : ℝ) P1.zW := by
          refine ⟨one_div_pos.mpr (Real.cosh_pos t),?_⟩
          unfold P1.zW
          exact one_div_lt_one_div_of_lt (by linarith [GW_bounds.1]) hGW
        have hc : Real.cosh t=1/(1/Real.cosh t) := by simp
        exact ⟨(P1.V_analyticAt hz hc).differentiableAt,P1.abs_deriv_V_lt_one hz hc⟩

theorem V_differentiable : Differentiable ℝ V :=
  fun t => (V_differentiable_and_derivative_bound t).1

theorem abs_deriv_V_lt_one (t : ℝ) : |deriv V t|<1 :=
  (V_differentiable_and_derivative_bound t).2

end polyak.Boundary
