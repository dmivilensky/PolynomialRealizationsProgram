import krylov.Functions.HilbertPlaneMinimax
import krylov.Functions.ObjectiveCoordinates

/-!
Article: main_krylov, prop:Fcycle(iii), genuine physical n-dimensional fibre.
Use: pull the actual full Hilbert-plane cubic through the true SPD-root
coordinates, preserve whole search objectives, and compare actual normalized
full gradients with the exact planar lower bound. Source: true scalar
coordinate chain rule and the proved full-plane gradient projection.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic krylov.Nonlinear
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The true physical scalar cubic, with the common orthogonal quadratic
and an actual positive-root coordinate map. Article: prop:Fcycle(iii). -/
def metricHilbertPlaneObjective (S : E ≃L[ℝ] E) (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) : E → ℝ :=
  coordinateObjective S.symm (hilbertPlaneObjective e h m p r t)

/-- The inverse-root normalized actual physical Riesz gradient is exactly
the original full canonical gradient. Article: prop:Fcycle(iii). -/
theorem metricHilbertPlaneGradient_normalized (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    S.symm (gradient (metricHilbertPlaneObjective S e h m p r t) x)=
      gradient (hilbertPlaneObjective e h m p r t) (S x) := by
  rw [metricHilbertPlaneObjective,gradient_coordinateObjective S.symm hS _ _
    (hilbertPlaneObjective_hasFDerivAt e h m p r t (S x)).differentiableAt]
  change S.symm (S (gradient (hilbertPlaneObjective e h m p r t) (S x)))=_
  exact S.symm_apply_apply _

/-- Every unrestricted physical output obeys the exact true planar
gradient lower comparison in the original inverse-root metric.
Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlaneGradient_norm_lower (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (e h m : E)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) (hm : hilbertPlaneProject e h m=0)
    (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) :
    ‖gradient (planeCubicObjective p r t) (hilbertPlaneProject e h (S x))‖≤
      ‖S.symm (gradient (metricHilbertPlaneObjective S e h m p r t) x)‖ := by
  rw [metricHilbertPlaneGradient_normalized S hS]
  exact hilbertPlaneGradient_norm_lower e h m he hh heh hm p r t (S x)

/-- Equal binary observations give exactly equal actual physical values
and Riesz gradients at every sampled planar coordinate.
Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlaneObjective_sample_equal (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (x : E)
    (hx : (inner ℝ e (S x)=0 ∧ inner ℝ h (S x)=0) ∨
      (inner ℝ e (S x)=p ∧ inner ℝ h (S x)=0) ∨ (inner ℝ e (S x)=p ∧ inner ℝ h (S x)=r*p)) :
    metricHilbertPlaneObjective S e h m p r u x=metricHilbertPlaneObjective S e h m p r t x ∧
      gradient (metricHilbertPlaneObjective S e h m p r u) x=gradient (metricHilbertPlaneObjective S e h m p r t) x := by
  have hh := hilbertPlaneObjective_sample_equal e h m p r t u hobs (S x) hx
  refine ⟨hh.1,?_⟩
  apply S.symm.injective
  rw [metricHilbertPlaneGradient_normalized S hS,metricHilbertPlaneGradient_normalized S hS,hh.2]

omit [CompleteSpace E] in
/-- Entire actual physical exact-search line objectives agree, including
every middle line. Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlaneObjective_search_equal (S : E ≃L[ℝ] E) (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (x s : E)
    (hline : (inner ℝ h (S x)=0 ∧ inner ℝ h (S s)=0) ∨
      (inner ℝ e (S x)=p ∧ inner ℝ e (S s)=0)) :
    (fun α : ℝ => metricHilbertPlaneObjective S e h m p r u (x+α • s))=
      (fun α : ℝ => metricHilbertPlaneObjective S e h m p r t (x+α • s)) := by
  have hh := hilbertPlaneObjective_search_equal e h m p r t u hobs (S x) (S s) hline
  simpa only [metricHilbertPlaneObjective,coordinateObjective,map_add,map_smul,ContinuousLinearEquiv.symm_symm] using hh

/-- The entire rich physical transcript is exactly constant on the original
binary data fibre. Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlaneObjective_transcript_equal (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u)
    (x s : ℕ → E) (N : ℕ)
    (hpoints : ∀ i≤N, (inner ℝ e (S (x i))=0 ∧ inner ℝ h (S (x i))=0) ∨
      (inner ℝ e (S (x i))=p ∧ inner ℝ h (S (x i))=0) ∨ (inner ℝ e (S (x i))=p ∧ inner ℝ h (S (x i))=r*p))
    (hlines : ∀ i<N, (inner ℝ h (S (x i))=0 ∧ inner ℝ h (S (s i))=0) ∨
      (inner ℝ e (S (x i))=p ∧ inner ℝ e (S (s i))=0)) :
    functionSearchTranscript (metricHilbertPlaneObjective S e h m p r u) x s N=
      functionSearchTranscript (metricHilbertPlaneObjective S e h m p r t) x s N := by
  apply FunctionSearchTranscript.ext
  · rfl
  · rfl
  · funext i
    exact (metricHilbertPlaneObjective_sample_equal S hS e h m p r t u hobs _ (hpoints i.val (by omega))).1
  · funext i
    exact (metricHilbertPlaneObjective_sample_equal S hS e h m p r t u hobs _ (hpoints i.val (by omega))).2
  · funext i
    exact metricHilbertPlaneObjective_search_equal S e h m p r t u hobs _ _ (hlines i.val i.isLt)

end
end krylov.Functions
