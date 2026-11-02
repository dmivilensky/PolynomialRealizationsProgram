import krylov.Nonlinear.CanonicalAverages
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Article: main_krylov, thm:RFCS, exact mixed self-concordance coordinate transport.
Use: Derive the true canonical mixed differential inequality from the original
physical one under the actual self-adjoint inverse metric coordinate map.
Source: genuine Hessian/variation congruence and real inner-product symmetry.
-/

namespace krylov.Nonlinear
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine mixed self-concordance differential inequality is preserved exactly by a continuous linear metric coordinate equivalence whose inverse is self-adjoint.
Use: Apply the proved identity-normalized local Hessian constant to the actual physical function without assuming a separately transformed self-concordance bound.
Article: main_krylov, thm:RFCS, actual canonical self-concordance transfer.
Proof: Move the true inverse coordinate map across each real inner product by its symmetry; all four actual differential pairings then become precisely the original physical ones.
-/
theorem coordinate_mixed_selfConcordance (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.toLinearMap.IsSymmetric)
    (H : E → E →L[ℝ] E) (D : E → E →L[ℝ] E →L[ℝ] E) (y : E)
    (hsc : ∀ u v w : E, |inner ℝ v (D (T.symm y) u w)|≤
      2*Real.sqrt (inner ℝ u (H (T.symm y) u))*Real.sqrt (inner ℝ v (H (T.symm y) v))*
        Real.sqrt (inner ℝ w (H (T.symm y) w))) :
    ∀ u v w : E, |inner ℝ v (coordinateHessianVariation T D y u w)|≤
      2*Real.sqrt (inner ℝ u (coordinateDerivative T H y u))*
        Real.sqrt (inner ℝ v (coordinateDerivative T H y v))*Real.sqrt (inner ℝ w (coordinateDerivative T H y w)) := by
  have he (a b : E) : inner ℝ a (coordinateDerivative T H y b)=
      inner ℝ (T.symm a) (H (T.symm y) (T.symm b)) := by
    change inner ℝ a (T.symm.toContinuousLinearMap (H (T.symm y) (T.symm b)))=_
    exact (hT a _).symm
  intro u v w
  have hd : inner ℝ v (coordinateHessianVariation T D y u w)=
      inner ℝ (T.symm v) (D (T.symm y) (T.symm u) (T.symm w)) := by
    change inner ℝ v (T.symm.toContinuousLinearMap (D (T.symm y) (T.symm u) (T.symm w)))=_
    exact (hT v _).symm
  rw [hd,he u u,he v v,he w w]
  exact hsc (T.symm u) (T.symm v) (T.symm w)

end
end krylov.Nonlinear
