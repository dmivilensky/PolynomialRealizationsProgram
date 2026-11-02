import krylov.Functions.NativeCentreUpper
import krylov.Functions.PlanarRFCFBetaModel

/-!
Article: main_krylov, thm:Fplanar, independent base perturbation.
Use: retain the full independent beta interval in the actual observed-data
centre upper bound. The extra quadratic leaves the true observed defects
and terminal gradient unchanged. Its contribution at the centre is fourth
order, because the last-direction centre movement is cubic.
Source: exact scalar differentiation and the genuine centre formula.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
/-- The original actual endpoint data recover the same observable binary
coefficients for every independent beta. No beta or tensor coefficient is
provided to the observer. Article: main_krylov, thm:Fplanar. -/
theorem planeBetaObservedBinaryData_eq (p r β : ℝ) (hp : p≠0) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic) :
    let f := planeBetaCubicObjective p r β t
    let G := gradient f
    planeObservedBinaryData p r (f 0) (f (planeOfPair (p,0))) (f (planeOfPair (p,r*p)))
      (G 0) (G (planeOfPair (p,0))) (G (planeOfPair (p,r*p)))=observe r t := by
  dsimp only
  unfold planeObservedBinaryData observe
  congr 1 <;>
    simp [planeBetaCubicObjective,planeBetaCubicGradient_actual,
      planeCubicObjective,planarCubicObjective,planarReferenceQuadratic,planarValueFamily,
      planeCubicGradient_actual,planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,
      planeOfPair,pairOfPlane,PiLp.inner_apply,Fin.sum_univ_two] <;> field_simp [hp,hr] <;> ring

/-- The last-coordinate motion of the budgeted centre is uniformly cubic
on the entire actual tensor ball. Article: main_krylov, thm:Fplanar. -/
theorem budgetedPlaneCentreOutput_last_movement (B r : ℝ) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ p : ℝ, 0<p → ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      |(budgetedPlaneCentreOutput B r p (observe r (scaleBinaryCubic B t))) 1-r*p|≤M*p^3 := by
  obtain ⟨M,hM,hbound⟩ := planeTerminal_uniform_bounds r
  refine ⟨B^2*M^2,mul_pos (pow_pos hB _) (pow_pos hM _),?_⟩
  intro p hp t ht
  let u := planeCentreTensor r (observe r t)
  let v := planeTerminalOperator r u (planeTerminalRho r u)
  have hu : u.InBall := planeCentreTensor_inBall ht r
  have hv : |v 1|≤M^2 := by
    have hc : |v 1|≤‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v 1
    apply hc.trans
    exact ((planeTerminalOperator r u).le_opNorm _).trans
      (by nlinarith only [(hbound u hu).1,(hbound u hu).2,norm_nonneg (planeTerminalOperator r u),norm_nonneg (planeTerminalRho r u)])
  have hy : (planeCentreOutput r (B*p) (observe r t)) 1-r*(B*p)=(B*p)^3*v 1 := by
    dsimp only [planeCentreOutput,v,u]
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
      planeTerminalRho,planeOfPair,Matrix.cons_val_one,Matrix.cons_val_zero,mul_zero,sub_zero]
    ring
  have hbudget : (budgetedPlaneCentreOutput B r p (observe r (scaleBinaryCubic B t))) 1-r*p=B^2*p^3*v 1 := by
    rw [budgetedPlaneCentreOutput,scalePlaneObservation_inverse B r hB.ne']
    change B⁻¹*(planeCentreOutput r (B*p) (observe r t)) 1-r*p=_
    have hh : (planeCentreOutput r (B*p) (observe r t)) 1=r*(B*p)+(B*p)^3*v 1 := by linarith only [hy]
    rw [hh]
    field_simp [hB.ne']
    ring
  rw [hbudget,abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg B) (pow_nonneg hp.le 3))]
  have hh := mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg B) (pow_nonneg hp.le 3))
  exact hh.trans_eq (by ring)

/-- With an arbitrary independent base perturbation of order p, the
actual budgeted centre retains the exact sharp leading coefficient and
one uniform fourth-order remainder. Article: main_krylov, thm:Fplanar. -/
theorem budgetedPlaneCentreOutput_beta_gradient_upper (B r L : ℝ) (hB : 0<B) (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 →
      ∀ β : ℝ, |β|≤L*p → ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ‖gradient (planeBetaCubicObjective p r β (scaleBinaryCubic B t))
        (budgetedPlaneCentreOutput B r p (observe r (scaleBinaryCubic B t)))‖≤
        B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4 := by
  obtain ⟨C,hC,hupper⟩ := budgetedPlaneCentreOutput_gradient_upper B r hB
  obtain ⟨M,hM,hmovement⟩ := budgetedPlaneCentreOutput_last_movement B r hB
  refine ⟨C+L*M,by nlinarith only [hC,mul_nonneg hL hM.le],?_⟩
  intro p hp hp₁ β hβ t ht
  rw [planeBetaCubicGradient_actual]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_mul]
  have he : ‖planeOfPair (0,1)‖=1 := by
    have hh := plane_norm_sq (planeOfPair (0,1))
    change ‖planeOfPair (0,1)‖^2=0^2+1^2 at hh
    nlinarith only [hh,norm_nonneg (planeOfPair (0,1))]
  rw [he,mul_one]
  have hb := mul_le_mul hβ (hmovement p hp t ht) (abs_nonneg _) (mul_nonneg hL hp.le)
  exact (add_le_add (hupper p hp hp₁ t ht) hb).trans_eq (by ring)

/-- An actual endpoint-only known-budget centre, including true exact
stationarity. All function and gradient samples are real oracle data.
Article: main_krylov, thm:Fplanar. -/
def planeBudgetObservedCentreOutput (B p r f₀ f₁ f₂ : ℝ) (g₀ g₁ g₂ : Plane) : Plane := by
  classical
  exact if g₂=0 then planeOfPair (p,r*p) else
    budgetedPlaneCentreOutput B r p (planeObservedBinaryData p r f₀ f₁ f₂ g₀ g₁ g₂)

/-- The fully observed original centre policy has the sharp uniform upper
bound on the whole independent beta class, with the correct known tensor
budget and a true fourth-order function remainder. Article: thm:Fplanar. -/
theorem planeBudgetObservedCentreOutput_beta_gradient_upper
    (B r L : ℝ) (hB : 0<B) (hr : r≠0) (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 →
      ∀ β : ℝ, |β|≤L*p → ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      let f := planeBetaCubicObjective p r β (scaleBinaryCubic B t)
      let G := gradient f
      let x := planeBudgetObservedCentreOutput B p r (f 0) (f (planeOfPair (p,0))) (f (planeOfPair (p,r*p)))
        (G 0) (G (planeOfPair (p,0))) (G (planeOfPair (p,r*p)))
      ‖G x‖≤B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4 := by
  classical
  obtain ⟨C,hC,hupper⟩ := budgetedPlaneCentreOutput_beta_gradient_upper B r L hB hL
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ β hβ t ht
  dsimp only
  unfold planeBudgetObservedCentreOutput
  split
  · rename_i hg
    rw [hg,norm_zero]
    have hm := (fibreMinimax_bounds r).1
    positivity
  · rw [planeBetaObservedBinaryData_eq p r β hp.ne' hr]
    exact hupper p hp hp₁ β hβ t ht

end
end krylov.Functions
