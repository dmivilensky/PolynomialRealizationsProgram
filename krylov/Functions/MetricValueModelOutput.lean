import krylov.Functions.ObjectiveCoordinates
import krylov.Functions.TrapezoidAffine
import krylov.Methods.CanonicalWindows

/-!
Article: main_krylov, thm:Fplanar, physical actual value-model covariance.
Use: transport the literal endpoint-value correction solve through a genuine
self-adjoint metric coordinate equivalence. The actual split, whole model,
right-hand side and returned point commute exactly, including singular
models under the existing totalized inverse convention.
Source: actual gradient chain rule and proved affine value-model invariance.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]

/-- The actual observed model-metric split of a scalar source.
Article: main_krylov, thm:Fplanar. -/
def observedValueModelSplit (f : E → ℝ) (a s : ι → E) (x : E) (i : ι) : ℝ :=
  covectorSplit (innerSL ℝ (gradient f (a i+s i)-gradient f (a i))) (a i) (s i) x

/-- The literal value-informed model output using actual scalar observations.
Article: main_krylov, thm:Fplanar. -/
def observedValueModelOutput (f : E → ℝ) (a s : ι → E) (x : E) : E :=
  x+combine s (modelCoefficients s (valueCorrectedModel f (fun y=>innerSL ℝ (gradient f y))
    a s (observedValueModelSplit f a s x)) (gradient f x))

/-- The true pulled-back scalar gradient gives the exact pulled-back covector.
Article: main_krylov, thm:Fplanar, genuine observed coordinate dictionary. -/
theorem metricValueGradient_covector (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (f : E → ℝ)
    (hdf : ∀ z, DifferentiableAt ℝ f z) (x : E) :
    innerSL ℝ (gradient (coordinateObjective S.symm f) x)=
      (innerSL ℝ (gradient f (S x))).comp S.toContinuousLinearMap := by
  rw [gradient_coordinateObjective S.symm hS f x (hdf (S x))]
  apply ContinuousLinearMap.ext
  intro v
  change inner ℝ (S (gradient f (S x))) v=inner ℝ (gradient f (S x)) (S v)
  exact hS _ _

omit [Fintype ι] [LinearOrder ι] [DecidableEq ι] in
/-- The actual model-metric splits commute with a true metric pullback.
Article: main_krylov, thm:Fplanar. -/
theorem observedValueModelSplit_metric (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (f : E → ℝ)
    (hdf : ∀ z, DifferentiableAt ℝ f z) (a s : ι → E) (x : E) :
    observedValueModelSplit (coordinateObjective S.symm f) a s x=
      observedValueModelSplit f (fun i=>S (a i)) (fun i=>S (s i)) (S x) := by
  funext i
  have hcov : innerSL ℝ (gradient (coordinateObjective S.symm f) (a i+s i)-
      gradient (coordinateObjective S.symm f) (a i))=
      (innerSL ℝ (gradient f (S (a i)+S (s i))-gradient f (S (a i)))).comp S.toContinuousLinearMap := by
    rw [map_sub,metricValueGradient_covector S hS f hdf,metricValueGradient_covector S hS f hdf,map_add]
    ext v
    simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,innerSL_apply_apply,inner_sub_left]
  unfold observedValueModelSplit
  rw [hcov,covectorSplit_affine _ S.toContinuousLinearMap 0]
  simp only [zero_add]
  rfl

/-- The whole actually observed value-corrected model is invariant under
physical metric pullback. Article: main_krylov, thm:Fplanar. -/
theorem observedValueModel_metric (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (f : E → ℝ)
    (hdf : ∀ z, DifferentiableAt ℝ f z) (a s : ι → E) (x : E) :
    valueCorrectedModel (coordinateObjective S.symm f)
      (fun y=>innerSL ℝ (gradient (coordinateObjective S.symm f) y)) a s
      (observedValueModelSplit (coordinateObjective S.symm f) a s x)=
    valueCorrectedModel f (fun y=>innerSL ℝ (gradient f y))
      (fun i=>S (a i)) (fun i=>S (s i)) (observedValueModelSplit f (fun i=>S (a i)) (fun i=>S (s i)) (S x)) := by
  have hd : (fun y=>innerSL ℝ (gradient (coordinateObjective S.symm f) y))=
      (fun y=>(innerSL ℝ (gradient f (0+S y))).comp S.toContinuousLinearMap) := by
    funext y
    simpa only [zero_add] using metricValueGradient_covector S hS f hdf y
  rw [hd,observedValueModelSplit_metric S hS f hdf]
  have hh := valueCorrectedModel_affine f (fun y=>innerSL ℝ (gradient f y)) S.toContinuousLinearMap 0 a s
    (observedValueModelSplit f (fun i=>S (a i)) (fun i=>S (s i)) (S x))
  have hf : coordinateObjective S.symm f=(fun y=>f (S y)) := by
    funext y
    rfl
  rw [hf]
  convert! hh using 1 <;> simp only [zero_add,ContinuousLinearEquiv.coe_coe]

/-- The actual value-informed returned point commutes exactly with metric
coordinates, with every split and model computed from real observations.
Article: main_krylov, thm:Fplanar, physical native solve reduction. -/
theorem observedValueModelOutput_metric (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (f : E → ℝ)
    (hdf : ∀ z, DifferentiableAt ℝ f z) (a s : ι → E) (x : E) :
    S (observedValueModelOutput (coordinateObjective S.symm f) a s x)=
      observedValueModelOutput f (fun i=>S (a i)) (fun i=>S (s i)) (S x) := by
  have hcoords : coordinates s (gradient (coordinateObjective S.symm f) x)=
      coordinates (fun i=>S (s i)) (gradient f (S x)) := by
    rw [gradient_coordinateObjective S.symm hS f x (hdf (S x))]
    ext i
    change inner ℝ (s i) (S (gradient f (S x)))=inner ℝ (S (s i)) (gradient f (S x))
    exact (hS _ _).symm
  unfold observedValueModelOutput
  rw [map_add,observedValueModel_metric S hS f hdf]
  simp only [modelCoefficients,hcoords,combine,map_sum,map_smul]

end
end krylov.Functions
