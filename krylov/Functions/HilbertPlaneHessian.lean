import krylov.Functions.HilbertPlaneObjective
import krylov.Functions.PlanarHessianFields

/-!
Article: main_krylov, prop:Fcycle(iii), true full-space Hessian and third tensor.
Use: retain the exact planar differential block and add the identity on its
actual orthogonal complement. Source: genuine chain rules and orthogonal
energy decomposition, rather than assumed full-space derivative fields.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The actual adjoint relation in its right-action form. Article: prop:Fcycle(iii). -/
theorem hilbertPlane_adjoint_right (e h x : E) (z : Plane) :
    inner ℝ x (hilbertPlaneEmbed e h z)=inner ℝ (hilbertPlaneProject e h x) z := by
  rw [real_inner_comm,hilbertPlane_adjoint,real_inner_comm]

/-- The genuine continuous linear lift of one true planar operator.
Article: main_krylov, prop:Fcycle(iii). -/
def hilbertPlaneLiftOperator (e h : E) : (Plane →L[ℝ] Plane) →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E Plane E (hilbertPlaneEmbed e h)).comp
    ((ContinuousLinearMap.compL ℝ E Plane Plane).flip (hilbertPlaneProject e h))

/-- The genuine full scalar cubic Hessian. Article: prop:Fcycle(iii). -/
def hilbertPlaneHessian (e h : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) : E →L[ℝ] E :=
  hilbertPlaneLiftOperator e h (planeCubicHessian p r t (hilbertPlaneProject e h x))+
    (ContinuousLinearMap.id ℝ E-(hilbertPlaneEmbed e h).comp (hilbertPlaneProject e h))

/-- The actual constant third variation of the full scalar cubic.
Article: main_krylov, prop:Fcycle(iii). -/
def hilbertPlaneVariation (e h : E) (t : krylov.Tensor.BinaryCubic) : E →L[ℝ] E →L[ℝ] E :=
  (hilbertPlaneLiftOperator e h).comp ((canonicalVariation t.tensor).comp (hilbertPlaneProject e h))

/-- Differentiating the actual full Riesz gradient gives the stated true
Hessian. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_hasFDerivAt (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    HasFDerivAt (gradient (hilbertPlaneObjective e h m p r t)) (hilbertPlaneHessian e h p r t x) x := by
  have hp := (planeCubicGradient_hasFDerivAt p r t (hilbertPlaneProject e h x)).comp x
    (hilbertPlaneProject e h).hasFDerivAt
  have hh := ((((hilbertPlaneEmbed e h).hasFDerivAt.comp x hp).add (hasFDerivAt_id x)).sub
    ((hilbertPlaneEmbed e h).comp (hilbertPlaneProject e h)).hasFDerivAt).sub_const m
  convert! hh using 1
  · funext y
    exact hilbertPlaneGradient_actual e h m p r t y
  · apply ContinuousLinearMap.ext
    intro v
    simp only [hilbertPlaneHessian,hilbertPlaneLiftOperator,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,_root_.add_apply,
      _root_.sub_apply,ContinuousLinearMap.id_apply]
    abel

omit [CompleteSpace E] in
/-- Differentiating the true full Hessian gives its true constant third
variation. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_hasFDerivAt (e h : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    HasFDerivAt (hilbertPlaneHessian e h p r t) (hilbertPlaneVariation e h t) x := by
  exact (((hilbertPlaneLiftOperator e h).hasFDerivAt.comp x
    ((planeCubicHessian_hasFDerivAt p r t (hilbertPlaneProject e h x)).comp x
      (hilbertPlaneProject e h).hasFDerivAt)).add_const
    (ContinuousLinearMap.id ℝ E-(hilbertPlaneEmbed e h).comp (hilbertPlaneProject e h)))

omit [CompleteSpace E] in
/-- The actual Hessian pairing is its exact planar part plus the common
orthogonal quadratic part. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_pair (e h : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x v w : E) :
    inner ℝ v (hilbertPlaneHessian e h p r t x w)=
      inner ℝ (hilbertPlaneProject e h v) (planeCubicHessian p r t (hilbertPlaneProject e h x) (hilbertPlaneProject e h w))+
        inner ℝ v w-inner ℝ (hilbertPlaneProject e h v) (hilbertPlaneProject e h w) := by
  simp only [hilbertPlaneHessian,hilbertPlaneLiftOperator,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,_root_.add_apply,
    _root_.sub_apply,ContinuousLinearMap.id_apply,inner_add_right,inner_sub_right,hilbertPlane_adjoint_right]
  ring

omit [CompleteSpace E] in
/-- The actual third contraction is exactly the true planar contraction.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneVariation_pair (e h : E) (t : krylov.Tensor.BinaryCubic) (u v w : E) :
    inner ℝ v (hilbertPlaneVariation e h t u w)=
      t.tensor.form (hilbertPlaneProject e h u) (hilbertPlaneProject e h v) (hilbertPlaneProject e h w) := by
  change inner ℝ v (hilbertPlaneEmbed e h
    (canonicalVariation t.tensor (hilbertPlaneProject e h u) (hilbertPlaneProject e h w)))=_
  rw [hilbertPlane_adjoint_right,canonicalVariation_pair]

omit [CompleteSpace E] in
/-- The full quadratic remainder is the genuine nonnegative orthogonal
energy. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlane_residual_norm_sq (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (v : E) :
    ‖v-hilbertPlaneEmbed e h (hilbertPlaneProject e h v)‖^2=
      ‖v‖^2-‖hilbertPlaneProject e h v‖^2 := by
  rw [norm_sub_sq_real,hilbertPlaneEmbed_norm e h he hh heh,hilbertPlane_adjoint_right,
    real_inner_self_eq_norm_sq]
  ring

omit [CompleteSpace E] in
/-- The actual full Hessian has precisely the planar metric plus positive
orthogonal energy. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_energy (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x v : E) :
    inner ℝ v (hilbertPlaneHessian e h p r t x v)=
      inner ℝ (hilbertPlaneProject e h v) (planeCubicHessian p r t (hilbertPlaneProject e h x) (hilbertPlaneProject e h v))+
        ‖v-hilbertPlaneEmbed e h (hilbertPlaneProject e h v)‖^2 := by
  rw [hilbertPlaneHessian_pair,hilbertPlane_residual_norm_sq e h he hh heh]
  simp only [real_inner_self_eq_norm_sq]
  ring

end
end krylov.Functions
