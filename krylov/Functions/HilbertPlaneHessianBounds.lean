import krylov.Functions.HilbertPlaneHessian
import krylov.Functions.PlanarSourceShrink
import krylov.Functions.ExactSearchOperator

/-!
Article: main_krylov, prop:Fcycle(iii), original positive search domain.
Use: derive a single actual positive-Hessian ball for all genuine bounded
binary cubic sources and all sufficiently small cycle scales. This gives
real exact-search uniqueness before a native trajectory is identified.
Source: exact orthogonal block lift and genuine bounded planar tensor ball.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Lifting a true planar operator into an orthonormal full-space plane
cannot increase its actual operator norm. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneLiftOperator_norm (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (A : Plane →L[ℝ] Plane) :
    ‖hilbertPlaneLiftOperator e h A‖≤‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖hilbertPlaneEmbed e h (A (hilbertPlaneProject e h v))‖≤‖A‖*‖v‖
  rw [hilbertPlaneEmbed_norm e h he hh heh]
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (hilbertPlaneProject_norm_le e h he hh heh v) (norm_nonneg _))

omit [CompleteSpace E] in
/-- The actual full Hessian perturbation is precisely the true planar
Hessian perturbation lifted into the plane. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_sub_id (e h : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    hilbertPlaneHessian e h p r t x-ContinuousLinearMap.id ℝ E=
      hilbertPlaneLiftOperator e h
        (planeCubicHessian p r t (hilbertPlaneProject e h x)-ContinuousLinearMap.id ℝ Plane) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [hilbertPlaneHessian,hilbertPlaneLiftOperator,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,_root_.add_apply,
    _root_.sub_apply,ContinuousLinearMap.id_apply,map_sub]
  abel

omit [CompleteSpace E] in
/-- The true full Hessian distortion is bounded by its true planar block
distortion, with constant one. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_norm_sub_id (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) :
    ‖hilbertPlaneHessian e h p r t x-ContinuousLinearMap.id ℝ E‖≤
      ‖planeCubicHessian p r t (hilbertPlaneProject e h x)-ContinuousLinearMap.id ℝ Plane‖ := by
  rw [hilbertPlaneHessian_sub_id]
  exact hilbertPlaneLiftOperator_norm e h he hh heh _

omit [CompleteSpace E] in
/-- A common genuine search ball has positive actual Hessian for every
admissible binary tensor and every bounded coefficient shrink, at all
sufficiently small cycle scales. No query location or CG path is assumed.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_uniform_positive_ball (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (r U : ℝ) (hU : 0<U) :
    ∃ R ep : ℝ, 0<R ∧ 0<ep ∧ ∀ p : ℝ, 0<p → p<ep → ∀ α : ℝ, 0≤α → α≤U →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall → ∀ x : E, ‖x‖≤R → ∀ v : E,
        ‖v‖^2/2 ≤ inner ℝ v (hilbertPlaneHessian e h p r (scaleBinaryCubic α t) x v) := by
  obtain ⟨M,hM,hbound⟩ := planeTerminal_uniform_bounds r
  let b := ‖planeOfPair (1,r)‖
  let R := 1/(8*(U+1))
  let ep := 1/(8*(U*(M+b)+1))
  have hb : 0≤b := norm_nonneg _
  have hR : 0<R := by dsimp only [R]; positivity
  have hep : 0<ep := by dsimp only [ep]; positivity
  refine ⟨R,ep,hR,hep,?_⟩
  intro p hp hpe α hα hαU t ht x hx v
  have hRsmall : U*R≤1/8 := by
    have heq : 8*(U+1)*R=1 := by dsimp only [R]; field_simp
    nlinarith only [heq,hR]
  have hpsmall : U*(M+b)*p≤1/8 := by
    have heq : 8*(U*(M+b)+1)*ep=1 := by dsimp only [ep]; field_simp
    have hh := mul_le_mul_of_nonneg_left hpe.le (by positivity : 0≤8*(U*(M+b)+1))
    nlinarith only [heq,hh,hp]
  have hlast : ‖planeOfPair (p,r*p)‖=p*b := by
    have heq : planeOfPair (p,r*p)=p • planeOfPair (1,r) := by
      rw [←planeOfPair_smul]
      congr 1
      ext <;> simp [mul_comm]
    rw [heq,norm_smul,Real.norm_of_nonneg hp.le]
  have hcoord : ‖hilbertPlaneProject e h x-planeOfPair (p,r*p)‖≤R+p*b := by
    apply (norm_sub_le _ _).trans
    rw [hlast]
    exact add_le_add ((hilbertPlaneProject_norm_le e h he hh heh x).trans hx) le_rfl
  have hn : ‖hilbertPlaneHessian e h p r (scaleBinaryCubic α t) x-ContinuousLinearMap.id ℝ E‖≤1/2 := by
    calc
      _ ≤ α*p*‖planeTerminalOperator r t‖+α*‖hilbertPlaneProject e h x-planeOfPair (p,r*p)‖ :=
        (hilbertPlaneHessian_norm_sub_id e h he hh heh p r _ x).trans
          (planeCubicHessian_scaled_norm_sub_id p r α hp.le hα ht _)
      _ ≤ U*p*M+U*(R+p*b) := by gcongr; exact (hbound t ht).1
      _ ≤ 1/2 := by nlinarith only [hRsmall,hpsmall]
  exact inner_lower_of_identity_bound _ hn v

end
end krylov.Functions
