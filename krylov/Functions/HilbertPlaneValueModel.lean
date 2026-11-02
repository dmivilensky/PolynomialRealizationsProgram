import krylov.Functions.HilbertPlaneObjective
import krylov.Functions.PlanarRFCFModel

/-!
Article: main_krylov, thm:Fplanar, genuine full-space value-model reduction.
Use: retain the actual endpoint values and gradients when adjoining a
positive quadratic orthogonal complement to the original planar cubic.
Source: the true scalar differential, adjoint plane coordinates and exact
quadratic trapezoid cancellation.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual full-space source has exactly the original planar scalar
trapezoid defect: its common complement is quadratic.
Article: main_krylov, thm:Fplanar, genuine observed-value reduction. -/
theorem hilbertPlane_value_defect (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (a s : E) :
    segmentValueDefect (hilbertPlaneObjective e h m p r t)
      (fun x=>innerSL ℝ (gradient (hilbertPlaneObjective e h m p r t) x)) a s=
    segmentValueDefect (planeCubicObjective p r t)
      (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
      (hilbertPlaneProject e h a) (hilbertPlaneProject e h s) := by
  simp only [segmentValueDefect,hilbertPlaneObjective,hilbertPlaneGradient_actual,hilbertPlaneGradient,
    innerSL_apply_apply,inner_sub_left,inner_add_left,hilbertPlane_adjoint,map_add,norm_add_sq_real,
    inner_add_right,real_inner_self_eq_norm_sq]
  ring

/-- Every actual full-space gradient secant pairing is its planar pairing
plus precisely the common orthogonal-complement Gram pairing.
Article: main_krylov, thm:Fplanar, actual full-model block dictionary. -/
theorem hilbertPlane_secant_pair (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s v : E) :
    inner ℝ (gradient (hilbertPlaneObjective e h m p r t) (a+s)-
      gradient (hilbertPlaneObjective e h m p r t) a) v=
    inner ℝ s v-inner ℝ (hilbertPlaneProject e h s) (hilbertPlaneProject e h v)+
      inner ℝ (gradient (planeCubicObjective p r t)
          (hilbertPlaneProject e h a+hilbertPlaneProject e h s)-
        gradient (planeCubicObjective p r t) (hilbertPlaneProject e h a))
        (hilbertPlaneProject e h v) := by
  simp only [hilbertPlaneGradient_actual,hilbertPlaneGradient,inner_sub_left,inner_add_left,
    hilbertPlane_adjoint,map_add]
  ring

set_option maxHeartbeats 800000 in
/-- The complete actual value-corrected model is the true complement Gram
plus the original planar value model. This holds for the actual chosen
splits and arbitrary original anchors, without assuming model block entries.
Article: main_krylov, thm:Fplanar, actual full-space model reduction. -/
theorem hilbertPlane_value_model {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (e h m : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (a s : ι → E) (l : ι → ℝ) :
    valueCorrectedModel (hilbertPlaneObjective e h m p r t)
      (fun x=>innerSL ℝ (gradient (hilbertPlaneObjective e h m p r t) x)) a s l=
    crossGram s s+
      valueCorrectedModel (planeCubicObjective p r t)
        (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
        (fun i=>hilbertPlaneProject e h (a i)) (fun i=>hilbertPlaneProject e h (s i)) l-
      crossGram (fun i=>hilbertPlaneProject e h (s i)) (fun i=>hilbertPlaneProject e h (s i)) := by
  ext i j
  simp only [valueCorrectedModel,krylov.Secant.latest,Matrix.add_apply,Matrix.sub_apply,
    _root_.sub_apply,innerSL_apply_apply,←inner_sub_left,hilbertPlane_secant_pair]
  by_cases hij : i=j
  · subst j
    simp only [min_self,max_self,diagonal_apply_eq,hilbertPlane_value_defect,crossGram]
    ring
  · simp only [diagonal_apply_ne _ hij,sub_zero,crossGram]
    rcases le_total i j with hle | hle
    · simp only [min_eq_left hle,max_eq_right hle]
      rw [real_inner_comm (s j) (s i),real_inner_comm (hilbertPlaneProject e h (s j)) (hilbertPlaneProject e h (s i))]
      ring
    · simp only [min_eq_right hle,max_eq_left hle]
      ring

end
end krylov.Functions
