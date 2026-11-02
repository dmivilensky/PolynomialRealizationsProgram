import krylov.Functions.FCOwnCanonical

/-!
Article: main_krylov, thm:LB, actual true-minimizer metric replacement.
Use: compare every possible output gradient and the genuine rank-one
canonical tensor budget uniformly in all nearby positive Hessians.
No regularity or localization of the method output or the parameter
selection is assumed. Source: actual CFC square-root continuity on the
positive cone, true inverse-root algebra and the operator norm inequality.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric Filter Topology krylov.Reference krylov.Functions krylov.Secant
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The real inverse-root field is continuous on the actual SPD cone.
Article: main_krylov, thm:LB, genuine true-metric normalization. -/
theorem oneGradient_inverseRoot_continuousWithinAt
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ContinuousWithinAt (fun B : Matrix (Fin n) (Fin n) ℝ=>cgOperator (metricRoot B)⁻¹)
      {B | B.PosDef} A := by
  have hsqrt : ContinuousWithinAt (fun B : Matrix (Fin n) (Fin n) ℝ=>CFC.sqrt B) {B | 0≤B} A :=
    CFC.continuousOn_sqrt _ hA.posSemidef.nonneg
  have hroot : ContinuousWithinAt (fun B : Matrix (Fin n) (Fin n) ℝ=>metricRoot B) {B | B.PosDef} A :=
    hsqrt.mono (fun _ hB=>hB.posSemidef.nonneg)
  have hu : IsUnit (metricRoot A) := (Matrix.isUnit_iff_isUnit_det _).mpr (metricRoot_det_unit A hA)
  have hi := contDiffAt_ringInverse (n:=1) ℝ hu.unit
  rw [hu.unit_spec] at hi
  have hinv : ContinuousWithinAt (fun B : Matrix (Fin n) (Fin n) ℝ=>(metricRoot B)⁻¹) {B | B.PosDef} A := by
    simpa only [Function.comp_def,←Matrix.nonsing_inv_eq_ringInverse] using
      hi.continuousAt.comp_continuousWithinAt (f:=fun B : Matrix (Fin n) (Fin n) ℝ=>metricRoot B) hroot
  let P := (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  exact P.continuous.continuousAt.comp_continuousWithinAt (f:=fun B : Matrix (Fin n) (Fin n) ℝ=>(metricRoot B)⁻¹) hinv

/-- Every actual gradient, however large or small, changes by at most a
prescribed relative factor in every sufficiently nearby positive metric.
Article: main_krylov, thm:LB, uniform arbitrary-output normalization. -/
theorem oneGradient_dual_metric_relative_neighborhood
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef → ‖B-A‖≤δ →∀ v : E,
      (1-η)*‖cgOperator (metricRoot A)⁻¹ v‖≤‖cgOperator (metricRoot B)⁻¹ v‖ ∧
        ‖cgOperator (metricRoot B)⁻¹ v‖≤(1+η)*‖cgOperator (metricRoot A)⁻¹ v‖ := by
  let S := cgOperator (metricRoot A)
  let RA := cgOperator (metricRoot A)⁻¹
  let F := fun B : Matrix (Fin n) (Fin n) ℝ=>cgOperator (metricRoot B)⁻¹*S-ContinuousLinearMap.id ℝ E
  have hF : ContinuousWithinAt F {B | B.PosDef} A :=
    ((oneGradient_inverseRoot_continuousWithinAt A hA).mul continuousWithinAt_const).sub continuousWithinAt_const
  have hF0 : F A=0 := by
    dsimp only [F,S]
    simp only [cgOperator]
    rw [←map_mul,Matrix.nonsing_inv_mul _ (metricRoot_det_unit A hA),map_one]
    exact sub_self _
  have hnear : ∀ᶠ B in 𝓝[{B | B.PosDef}] A,‖F B‖<η := by
    have hh := hF.norm.eventually (gt_mem_nhds (show ‖F A‖<η by rw [hF0,norm_zero];exact hη))
    exact hh
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro B hB hBA v
  have hFsmall : ‖F B‖≤η := (hbound ⟨by rw [mem_ball,dist_eq_norm];exact hBA.trans_lt (half_lt_self hδ),hB⟩).le
  have hcancel : S (RA v)=v := by
    dsimp only [S,RA,cgOperator]
    rw [←mul_apply_eq_comp,←map_mul,Matrix.mul_nonsing_inv _ (metricRoot_det_unit A hA),map_one,one_apply_eq_self]
  have hh := ((F B).le_opNorm (RA v)).trans (mul_le_mul_of_nonneg_right hFsmall (norm_nonneg _))
  change ‖cgOperator (metricRoot B)⁻¹ (S (RA v))-RA v‖≤η*‖RA v‖ at hh
  rw [hcancel] at hh
  have hn := abs_norm_sub_norm_le (cgOperator (metricRoot B)⁻¹ v) (RA v)
  have hb := abs_le.mp (hn.trans hh)
  constructor <;> nlinarith only [hb.1,hb.2]

/-- The actual canonical rank-one tensor budget changes by only the cube
of the same relative metric factor. Article: main_krylov, thm:LB. -/
theorem oneGradient_rankOne_budget_metric_transfer
    (A B : Matrix (Fin n) (Fin n) ℝ) (a : E) (t M η : ℝ) (_hM : 0≤M) (hη : 0≤η)
    (hbudget : |t| *‖cgOperator (metricRoot A)⁻¹ a‖^3≤M)
    (haxis : ‖cgOperator (metricRoot B)⁻¹ a‖≤(1+η)*‖cgOperator (metricRoot A)⁻¹ a‖) :
    |t| *‖cgOperator (metricRoot B)⁻¹ a‖^3≤(1+η)^3*M := by
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) haxis 3) (abs_nonneg t)
  have hb := mul_le_mul_of_nonneg_left hbudget (by positivity : 0≤(1+η)^3)
  rw [mul_pow] at hh
  nlinarith only [hh,hb]

end
end krylov.Convergence
