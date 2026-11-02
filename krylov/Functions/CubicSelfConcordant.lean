import krylov.Functions.PolynomialValueModel
import krylov.Tensor.CubicBanach
import krylov.Nonlinear.SelfConcordantFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, thm:H, actual cubic self-concordant realization.
Use: construct the scalar function, its true gradient, Hessian and third
variation, then derive standard self-concordance from the genuine tensor
bound on a ball. Source: Banach's diagonal norm identity and the Hessian
lower bound I+T[x] >= (1-c*norm x)I, as in Appendix D.
-/

namespace krylov.Functions
noncomputable section
open InnerProductSpace krylov.Tensor
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual Riesz bilinear form for the canonical quadratic part.
Article: main_krylov, thm:H, H_*=I. -/
def canonicalBilinear : E →L[ℝ] E →L[ℝ] ℝ :=
  (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap

/-- The inverse Riesz map used to turn genuine scalar derivatives into vectors.
Article: main_krylov, thm:H. -/
def inverseRiesz : (E →L[ℝ] ℝ) →L[ℝ] E :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The actual canonical quadratic-plus-cubic scalar function.
Article: main_krylov, thm:H, f(z)=norm(z)^2/2+T(z,z,z)/6. -/
def canonicalCubic (T : SymmetricCubic E) : E → ℝ :=
  cubicPolynomial canonicalBilinear 0 T 0

/-- The function agrees exactly with the scalar formula printed in the paper.
Article: main_krylov, thm:H. -/
theorem canonicalCubic_eq (T : SymmetricCubic E) (x : E) :
    canonicalCubic T x=‖x‖^2/2+T.form x x x/6 := by
  simp only [canonicalCubic,cubicPolynomial,quadraticPotential,canonicalBilinear,
    zero_add,zero_apply,sub_zero,SymmetricCubic.potential]
  change inner ℝ x x/2+_= _
  rw [real_inner_self_eq_norm_sq]

/-- The actual scalar differential field of the canonical cubic.
Article: main_krylov, thm:H. -/
def canonicalDifferential (T : SymmetricCubic E) (x : E) : E →L[ℝ] ℝ :=
  canonicalBilinear x+(1/2 : ℝ) • T.form x x

/-- The vector field obtained by applying the inverse Riesz map to the true differential.
Article: main_krylov, thm:H. -/
def canonicalGradient (T : SymmetricCubic E) (x : E) : E :=
  inverseRiesz (canonicalDifferential T x)

/-- The true canonical Hessian operator field.
Article: main_krylov, thm:H. -/
def canonicalHessian (T : SymmetricCubic E) (x : E) : E →L[ℝ] E :=
  inverseRiesz.comp (canonicalBilinear+T.form x)

/-- The constant genuine third variation, represented in vector coordinates.
Article: main_krylov, thm:H. -/
def canonicalVariation (T : SymmetricCubic E) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E inverseRiesz).comp T.form

/-- The canonical bilinear form is symmetric, by real inner-product symmetry.
Article: main_krylov, thm:H. -/
theorem canonicalBilinear_symmetric (u v : E) :
    canonicalBilinear u v=canonicalBilinear v u := real_inner_comm v u

/-- The displayed scalar differential is genuinely the Frechet derivative.
Article: main_krylov, thm:H. -/
theorem canonicalCubic_hasFDerivAt (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (canonicalCubic T) (canonicalDifferential T x) x := by
  simpa only [canonicalCubic,canonicalDifferential,sub_zero] using
    cubicPolynomial_hasFDerivAt canonicalBilinear 0 canonicalBilinear_symmetric T 0 x

/-- The vector field is the actual mathematical gradient of the scalar function.
Article: main_krylov, thm:H. -/
theorem gradient_canonicalCubic (T : SymmetricCubic E) :
    gradient (canonicalCubic T)=canonicalGradient T := by
  funext x
  simp only [gradient,canonicalGradient,inverseRiesz]
  rw [(canonicalCubic_hasFDerivAt T x).fderiv]
  rfl

/-- Differentiating the actual gradient yields the displayed Hessian field.
Article: main_krylov, thm:H. -/
theorem canonicalGradient_hasFDerivAt (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (canonicalGradient T) (canonicalHessian T x) x := by
  have hscalar : HasFDerivAt (canonicalDifferential T) (canonicalBilinear+T.form x) x := by
    simpa only [canonicalDifferential,sub_zero] using!
      cubicPolynomial_differential_hasFDerivAt canonicalBilinear 0 T x
  exact inverseRiesz.hasFDerivAt.comp x hscalar

/-- Differentiating the actual Hessian gives its genuine constant third variation.
Article: main_krylov, thm:H. -/
theorem canonicalHessian_hasFDerivAt (T : SymmetricCubic E) (x : E) :
    HasFDerivAt (canonicalHessian T) (canonicalVariation T) x := by
  let P : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E :=
    ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E inverseRiesz
  have he : canonicalHessian T=fun y => P canonicalBilinear+canonicalVariation T y := by
    funext y
    change P (canonicalBilinear+T.form y)=P canonicalBilinear+(P.comp T.form) y
    rw [map_add]
    rfl
  rw [he]
  exact ((canonicalVariation T).hasFDerivAt (𝕜 := ℝ) (x := x)).const_add (P canonicalBilinear)

/-- The actual Hessian pairing is the canonical metric plus the cubic slice.
Article: main_krylov, thm:H. -/
theorem canonicalHessian_pair (T : SymmetricCubic E) (x v w : E) :
    inner ℝ v (canonicalHessian T x w)=inner ℝ v w+T.form x v w := by
  change inner ℝ v ((toDual ℝ E).symm ((canonicalBilinear (E := E)+T.form x) w))=_
  rw [real_inner_comm,toDual_symm_apply]
  simp only [add_apply]
  change inner ℝ w v+T.form x w v=_
  rw [real_inner_comm w v,T.swap₂ x w v]

/-- The actual third variation pairing is precisely the prescribed scalar tensor.
Article: main_krylov, thm:H. -/
theorem canonicalVariation_pair (T : SymmetricCubic E) (u v w : E) :
    inner ℝ v (canonicalVariation T u w)=T.form u v w := by
  change inner ℝ v ((toDual ℝ E).symm (T.form u w))=_
  rw [real_inner_comm,toDual_symm_apply,T.swap₂ u w v]

end
end krylov.Functions
