import krylov.Convergence.OneGradientCubicTensor
import krylov.Functions.FCOwnCanonical
import krylov.Functions.RankOneCriticalUniform

/-!
Article: main_krylov, thm:LB, uniform genuine cubic source domain.
Use: construct actual local minimizers and true positive Hessians for
all bounded missing-pivot/cubic parameters, including the last-query
clipped twins. The real inverse and all uniform bounds are derived from
the original positive quadratic lower form; no minimizer, inverse bound
or parameter regularity is assumed.
Source: positive-form perturbation, finite SPD inverse algebra and the
explicit genuine rank-one critical branch already proved in Functions.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The genuine matrix of the original missing last-normal curvature.
Article: main_krylov, thm:LB. -/
def oneGradientCubicFibreMatrix (base : Matrix (Fin n) (Fin n) ℝ) (a : E) (b : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := physicalOperatorMatrix (cgOperator base+b • InnerProductSpace.rankOne ℝ a a)

/-- True coercivity controls the actual inverse, with no independent
conditioning assumption. Article: thm:LB, uniform inverse domain. -/
theorem oneGradient_inverse_norm_coercive
    (Q Rinv : E →L[ℝ] E) (m : ℝ) (hm : 0<m) (hQR : ∀ v,Q (Rinv v)=v)
    (hQ : ∀ v,m*‖v‖^2≤ inner ℝ v (Q v)) : ‖Rinv‖≤m⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hm.le)
  intro v
  have hh := hQ (Rinv v)
  rw [hQR] at hh
  have hb := real_inner_le_norm (Rinv v) v
  by_cases hz : Rinv v=0
  · rw [hz,norm_zero]
    positivity
  · have hp := norm_pos_iff.mpr hz
    have hi : m*‖Rinv v‖≤‖v‖ := by nlinarith only [hh,hb,hp]
    exact (le_inv_mul_iff₀ hm).mpr hi

/-- Every clipped missing curvature retains true positivity and a
uniform bound on its genuine physical inverse. Article: thm:LB. -/
theorem oneGradientCubicFibre_uniform_domain
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (a : E) (m δ b : ℝ)
    (hm : 0<m) (hbase : ∀ v,m*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hbnd : |b|≤δ) (hsmall : δ*‖a‖^2≤m/2) :
    let Q := cgOperator base+b • InnerProductSpace.rankOne ℝ a a
    let B := oneGradientCubicFibreMatrix base a b
    B.PosDef ∧ (∀ v,(m/2)*‖v‖^2≤ inner ℝ v (Q v)) ∧
      (∀ v,Q (cgOperator B⁻¹ v)=v) ∧ ‖cgOperator B⁻¹‖≤2/m := by
  let Q := cgOperator base+b • InnerProductSpace.rankOne ℝ a a
  let B := oneGradientCubicFibreMatrix base a b
  have hQB : cgOperator B=Q := physicalOperatorMatrix_operator _
  have hnorm : ‖Q-cgOperator base‖≤δ*‖a‖^2 := by
    dsimp only [Q]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,InnerProductSpace.norm_rankOne]
    nlinarith only [mul_le_mul_of_nonneg_right hbnd (sq_nonneg ‖a‖)]
  have hform (v : E) : (m/2)*‖v‖^2≤ inner ℝ v (Q v) := by
    have hh := rankOne_form_perturbation (cgOperator base) Q m (m/2) hbase (hnorm.trans hsmall) v
    nlinarith only [hh]
  have hB : B.PosDef := physicalOperatorMatrix_posDef Q (oneGradientCubicFibre_symmetric base hb a b)
    (fun v hv=>lt_of_lt_of_le (mul_pos (by positivity : 0<m/2) (sq_pos_of_pos (norm_pos_iff.mpr hv))) (hform v))
  have hd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit
  have hQR (v : E) : Q (cgOperator B⁻¹ v)=v := by
    rw [←hQB]
    have hh := congrArg (fun A=>cgOperator A v) (Matrix.mul_nonsing_inv B hd)
    simpa only [cgOperator,map_mul,mul_apply_eq_comp,map_one,one_apply_eq_self] using hh
  refine ⟨hB,hform,hQR,?_⟩
  have hh := oneGradient_inverse_norm_coercive Q (cgOperator B⁻¹) (m/2) (by positivity) hQR hform
  simpa only [B,inv_div] using hh

/-- All original clipped-cubic sources have actual local minimizers and
positive true Hessians, uniformly even for discontinuous query-dependent
parameters. The true metric differs from the endpoint base by the
explicit O(delta+M norm(g)) bound. Article: main_krylov, thm:LB. -/
theorem oneGradientCubicFibre_uniform_minimum
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g a : E)
    (m δ b t M R : ℝ) (hm : 0<m) (hM : 0≤M)
    (hbase : ∀ v,m*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hbnd : |b|≤δ) (hcurv : δ*‖a‖^2≤m/2) (ht : |t|≤M)
    (hsmall : 2*M*(2/m)^2*‖a‖^3*‖g‖≤1)
    (hball : 2*(2/m)*‖g‖≤R) (hpositive : M*‖a‖^3*R≤m/4) :
    ∃ x : E,oneGradientCubicFibreGradient (cgOperator base) g a b t x=0 ∧
      IsMinOn (oneGradientCubicFibreObjective base g a b t) {z | ‖z‖≤R} x ∧
      ‖x‖≤2*(2/m)*‖g‖ ∧
      ‖x+cgOperator (oneGradientCubicFibreMatrix base a b)⁻¹ g‖≤2*M*(2/m)^3*‖a‖^3*‖g‖^2 ∧
      ‖oneGradientCubicHessian (cgOperator base+b • InnerProductSpace.rankOne ℝ a a) a t x-cgOperator base‖≤
        δ*‖a‖^2+2*M*(2/m)*‖a‖^3*‖g‖ ∧
      ∀ v,(m/4)*‖v‖^2≤ inner ℝ v
        (oneGradientCubicHessian (cgOperator base+b • InnerProductSpace.rankOne ℝ a a) a t x v) := by
  let Q := cgOperator base+b • InnerProductSpace.rankOne ℝ a a
  let B := oneGradientCubicFibreMatrix base a b
  obtain ⟨_,hform,hQR,hRi⟩ := oneGradientCubicFibre_uniform_domain base hb a m δ b hm hbase hbnd hcurv
  have hpos : M*‖a‖^3*R≤(m/2)/2 := by linarith only [hpositive]
  have hh := rankOneCriticalPoint_uniform_minimum Q (cgOperator B⁻¹)
    (oneGradientCubicFibre_symmetric base hb a b) hQR g a t M (2/m) (m/2) R hM (by positivity)
    (by positivity) ht hRi hform hsmall hball hpos
  let x := rankOneCriticalPoint (cgOperator B⁻¹) g a t
  change oneGradientCubicGradient Q g a t x=0 ∧ _ at hh
  refine ⟨x,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_,?_⟩
  · have hnorm : ‖Q-cgOperator base‖≤δ*‖a‖^2 := by
      dsimp only [Q]
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,InnerProductSpace.norm_rankOne]
      nlinarith only [mul_le_mul_of_nonneg_right hbnd (sq_nonneg ‖a‖)]
    exact (norm_sub_le_norm_sub_add_norm_sub (oneGradientCubicHessian Q a t x) Q (cgOperator base)).trans
      ((add_le_add hh.2.2.2.2.1 hnorm).trans_eq (add_comm _ _))
  · simpa only [div_div,show (2:ℝ)*2=4 by norm_num] using hh.2.2.2.2.2

end
end krylov.Convergence
