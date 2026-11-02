import krylov.Functions.HilbertPlaneCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, prop:Fcycle(iii), full-space genuine scalar cubic lift.
Use: add a common positive quadratic on the actual orthogonal complement
and retain the exact Euclidean planar gradient at every arbitrary full-space
output. Source: the true Frechet chain rule, true Riesz gradient and Bessel.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine scalar objective obtained by adjoining the common orthogonal
quadratic to the full planar cubic family. Article: prop:Fcycle(iii).
For m perpendicular to the plane, the added term is ‖x-JCx-m‖²/2. -/
def hilbertPlaneObjective (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) : ℝ :=
  planeCubicObjective p r t (hilbertPlaneProject e h x)+
    (‖x‖^2-‖hilbertPlaneProject e h x‖^2)/2-inner ℝ m x+‖m‖^2/2

/-- The actual full-space gradient field of the lifted scalar cubic.
Article: main_krylov, prop:Fcycle(iii). -/
def hilbertPlaneGradient (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) : E :=
  hilbertPlaneEmbed e h (gradient (planeCubicObjective p r t) (hilbertPlaneProject e h x))+
    x-hilbertPlaneEmbed e h (hilbertPlaneProject e h x)-m

/-- The true planar scalar cubic is differentiable at every actual point.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicObjective_differentiable (p r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    Differentiable ℝ (planeCubicObjective p r t) := by
  unfold planeCubicObjective planarCubicObjective planarReferenceQuadratic planarValueFamily pairOfPlane
  fun_prop

omit [CompleteSpace E] in
/-- The displayed full vector genuinely differentiates the lifted scalar
objective. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_hasFDerivAt (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    HasFDerivAt (hilbertPlaneObjective e h m p r t) (innerSL ℝ (hilbertPlaneGradient e h m p r t x)) x := by
  let C := hilbertPlaneProject e h
  let J := hilbertPlaneEmbed e h
  let gp := gradient (planeCubicObjective p r t) (C x)
  have hp := ((planeCubicObjective_differentiable p r t (C x)).hasGradientAt.hasFDerivAt).comp x C.hasFDerivAt
  have hq := (((hasFDerivAt_id x).norm_sq).sub C.hasFDerivAt.norm_sq).const_mul (1/2 : ℝ)
  have hm := (innerSL ℝ m).hasFDerivAt (x:=x)
  have hd := ((hp.add hq).sub hm).add_const (‖m‖^2/2)
  convert! hd using 1
  · funext y
    dsimp only [hilbertPlaneObjective,C,Function.comp_apply,Pi.add_apply,Pi.sub_apply,id_eq]
    simp only [innerSL_apply_apply]
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp only [hilbertPlaneGradient,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,
      _root_.smul_apply,smul_eq_mul,innerSL_apply_apply,inner_add_left,inner_sub_left,
      hilbertPlane_adjoint,InnerProductSpace.toDual_apply_apply,ContinuousLinearMap.id_apply,id_eq]
    dsimp only [C]
    ring

/-- The displayed full vector is the actual mathematical Riesz gradient.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_actual (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    gradient (hilbertPlaneObjective e h m p r t) x=hilbertPlaneGradient e h m p r t x :=
  (show HasGradientAt _ _ _ from hilbertPlaneObjective_hasFDerivAt e h m p r t x).gradient

/-- Projection of the actual full gradient recovers the exact original
planar gradient, at every unrestricted output. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_project (e h m : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (hm : hilbertPlaneProject e h m=0)
    (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) :
    hilbertPlaneProject e h (gradient (hilbertPlaneObjective e h m p r t) x)=
      gradient (planeCubicObjective p r t) (hilbertPlaneProject e h x) := by
  rw [hilbertPlaneGradient_actual,hilbertPlaneGradient,map_sub,map_sub,map_add,
    hilbertPlaneProject_embed e h he hh heh,hilbertPlaneProject_embed e h he hh heh,hm]
  abel

/-- The original true planar gradient is a lower bound on the actual
full-space gradient, without any output localization hypothesis.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_norm_lower (e h m : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (hm : hilbertPlaneProject e h m=0)
    (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) :
    ‖gradient (planeCubicObjective p r t) (hilbertPlaneProject e h x)‖≤
      ‖gradient (hilbertPlaneObjective e h m p r t) x‖ := by
  rw [←hilbertPlaneGradient_project e h m he hh heh hm p r t x]
  exact hilbertPlaneProject_norm_le e h he hh heh _

end
end krylov.Functions
