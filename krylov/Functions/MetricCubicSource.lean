import krylov.Functions.CubicSelfConcordant
import krylov.Functions.ObjectiveCoordinates
import krylov.Nonlinear.CoordinateLipschitz

/-!
Article: main_krylov, thm:H, genuine physical cubic realization.
Use: pull the actual canonical quadratic-plus-cubic function back through
the true metric root, retaining its actual scalar gradient and all genuine
derivatives. This preserves the original physical n-atom reference.
Source: the actual Frechet chain rule and inverse metric congruence.
-/

namespace krylov.Functions
noncomputable section
open krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual physical objective of a canonical cubic under a true metric map.
Article: main_krylov, thm:H. -/
def metricCubicObjective (S : E ≃L[ℝ] E) (T : SymmetricCubic E) : E → ℝ :=
  coordinateObjective S.symm (canonicalCubic T)

/-- The actual physical Riesz gradient of the metric cubic.
Article: main_krylov, thm:H. -/
def metricCubicGradient (S : E ≃L[ℝ] E) (T : SymmetricCubic E) : E → E :=
  coordinateGradient S.symm (canonicalGradient T)

/-- The genuine physical Hessian field of the metric cubic.
Article: main_krylov, thm:H. -/
def metricCubicHessian (S : E ≃L[ℝ] E) (T : SymmetricCubic E) : E → E →L[ℝ] E :=
  coordinateDerivative S.symm (canonicalHessian T)

/-- The genuine constant physical third variation of the metric cubic.
Article: main_krylov, thm:H. -/
def metricCubicVariation (S : E ≃L[ℝ] E) (T : SymmetricCubic E) : E →L[ℝ] E →L[ℝ] E :=
  (coordinateCongruence S.symm).comp ((canonicalVariation T).comp S.toContinuousLinearMap)

/-- The displayed physical gradient is the true scalar differential.
Article: main_krylov, thm:H. -/
theorem metricCubicObjective_hasFDerivAt (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (metricCubicObjective S T) (innerSL ℝ (metricCubicGradient S T x)) x := by
  apply coordinateObjective_hasFDerivAt S.symm hS _ _ x
  rw [← gradient_canonicalCubic]
  exact (canonicalCubic_hasFDerivAt T (S x)).differentiableAt.hasGradientAt.hasFDerivAt

/-- The metric cubic vector field is its actual Riesz gradient.
Article: main_krylov, thm:H. -/
theorem gradient_metricCubicObjective (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (T : SymmetricCubic E) :
    gradient (metricCubicObjective S T) = metricCubicGradient S T := by
  funext x
  exact (show HasGradientAt (metricCubicObjective S T) (metricCubicGradient S T x) x from
    metricCubicObjective_hasFDerivAt S hS T x).gradient

/-- Differentiating the actual physical gradient gives the actual metric Hessian.
Article: main_krylov, thm:H. -/
theorem metricCubicGradient_hasFDerivAt (S : E ≃L[ℝ] E) (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (metricCubicGradient S T) (metricCubicHessian S T x) x :=
  coordinateGradient_hasFDerivAt S.symm _ _ x (canonicalGradient_hasFDerivAt T (S x))

/-- Differentiating the actual physical Hessian gives its true constant third variation.
Article: main_krylov, thm:H. -/
theorem metricCubicHessian_hasFDerivAt (S : E ≃L[ℝ] E) (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (metricCubicHessian S T) (metricCubicVariation S T) x :=
  coordinateDerivative_hasFDerivAt S.symm _ (fun _ => canonicalVariation T) x
    (canonicalHessian_hasFDerivAt T (S x))

/-- The actual metric cubic gradient vanishes at its true origin.
Article: main_krylov, thm:H. -/
theorem metricCubicGradient_zero (S : E ≃L[ℝ] E) (T : SymmetricCubic E) :
    metricCubicGradient S T 0 = 0 := by
  simp [metricCubicGradient, coordinateGradient, canonicalGradient, canonicalDifferential]

/-- The canonical cubic's true Hessian at the origin is the identity.
Article: main_krylov, thm:H. -/
theorem canonicalHessian_zero (T : SymmetricCubic E) :
    canonicalHessian T 0 = ContinuousLinearMap.id ℝ E := by
  ext v
  simp only [canonicalHessian, map_zero, ContinuousLinearMap.comp_apply,
    canonicalBilinear, inverseRiesz, ContinuousLinearMap.id_apply]
  change (InnerProductSpace.toDual ℝ E).symm ((InnerProductSpace.toDual ℝ E) v + 0) = v
  rw [add_zero]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply v

/-- The metric cubic Hessian normalizes back to the actual canonical Hessian.
Article: main_krylov, thm:H. -/
theorem coordinateDerivative_metricCubic (S : E ≃L[ℝ] E) (T : SymmetricCubic E) :
    coordinateDerivative S (metricCubicHessian S T) = canonicalHessian T := by
  funext z
  ext v
  change S.symm (S (canonicalHessian T (S (S.symm z)) (S (S.symm v)))) = _
  simp only [S.apply_symm_apply, S.symm_apply_apply]

/-- The actual physical third variation has exactly the original canonical
cubic slice after its true inverse-root congruence.
Article: main_krylov, thm:H. -/
theorem coordinateCongruence_metricCubicVariation (S : E ≃L[ℝ] E)
    (T : SymmetricCubic E) (v : E) :
    coordinateCongruence S (metricCubicVariation S T v) = canonicalVariation T (S v) := by
  ext w
  change S.symm (S (canonicalVariation T (S v) (S (S.symm w)))) = _
  simp only [S.apply_symm_apply, S.symm_apply_apply]

/-- Genuine canonical Hessian differences are the actual linear third slices.
Article: main_krylov, thm:H. -/
theorem canonicalHessian_sub (T : SymmetricCubic E) (x y : E) :
    canonicalHessian T x - canonicalHessian T y = canonicalVariation T (x-y) := by
  ext v
  simp only [canonicalHessian, canonicalVariation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, map_sub, sub_apply, add_apply]
  simp only [map_add]
  abel

/-- The true canonical Hessian is globally Lipschitz with its actual third
variation operator norm. Article: main_krylov, thm:H. -/
theorem metricCubicHessian_canonical_lipschitz (S : E ≃L[ℝ] E) (T : SymmetricCubic E) :
    LipschitzWith ‖canonicalVariation T‖₊ (coordinateDerivative S (metricCubicHessian S T)) := by
  rw [coordinateDerivative_metricCubic, lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [canonicalHessian_sub]
  exact (canonicalVariation T).le_opNorm (x-y)

end
end krylov.Functions
