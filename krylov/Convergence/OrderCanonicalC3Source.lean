import krylov.Convergence.OneGradientC3Source
import krylov.Nonlinear.CanonicalAverages

/-!
Article: main_krylov, thm:D, original C-three local source assumptions.
Use: derive the native canonical closed-ball Hessian Lipschitz domain and
its numerical small-radius condition from the genuine continuous third
derivative. These are conclusions, not extra source hypotheses.
Source: actual inverse-coordinate chain rule, local derivative boundedness,
convex mean-value inequality, and elementary radius shrinking.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Nonlinear
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous genuine third derivative provides exactly the native
canonical closed-ball source domain used by FC, RFC and DC.
Article: main_krylov, thm:D and apG:D, C3 scope. -/
theorem exists_canonical_hessian_lipschitz_closedBall
    (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E) (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r)
    (hD : ∀ z,‖T z‖<r → HasFDerivAt H (D z) z) (hDc : ContinuousAt D 0) :
    ∃ s : ℝ,∃ L : ℝ≥0,0<s ∧s<r ∧(L:ℝ)*s≤1/2 ∧
      LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 s) := by
  have hDc' : ContinuousAt (coordinateHessianVariation T D) 0 := by
    have hc : ContinuousAt (fun y=>D (T.symm y)) 0 := by
      have hc0 : ContinuousAt D (T.symm 0) := by rw [map_zero];exact hDc
      exact hc0.comp T.symm.continuous.continuousAt
    exact continuousAt_const.clm_comp (hc.clm_comp continuousAt_const)
  have hder : ∀ y∈ball (0:E) r,
      HasFDerivAt (coordinateDerivative T H) (coordinateHessianVariation T D y) y := by
    intro y hy
    apply coordinateDerivative_hasFDerivAt T H D y
    apply hD
    rw [T.apply_symm_apply]
    simpa only [mem_ball,dist_zero_right] using hy
  obtain ⟨s,L,hs,hsr,hLip⟩ := exists_hessian_lipschitz_ball (coordinateDerivative T H)
    (coordinateHessianVariation T D) hr hder hDc'
  let a:=min (s/2) (1/(4*((L:ℝ)+1)))
  have ha : 0<a := by dsimp only [a];positivity
  have har : a<r := ((min_le_left _ _).trans_lt (half_lt_self hs)).trans_le hsr
  have hLs : (L:ℝ)*a≤1/2 := by
    have hb : a≤1/(4*((L:ℝ)+1)) := min_le_right _ _
    have hp : 0<4*((L:ℝ)+1) := by positivity
    have hh := (le_div_iff₀ hp).mp hb
    have hL : 0≤(L:ℝ) := L.coe_nonneg
    have haa : 0≤a := ha.le
    nlinarith only [hh,hL,haa]
  refine ⟨a,L,ha,har,hLs,hLip.mono ?_⟩
  intro y hy
  rw [mem_closedBall,dist_zero_right] at hy
  rw [mem_ball,dist_zero_right]
  exact hy.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hs))

end
end krylov.Convergence
