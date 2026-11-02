import krylov.Stability.AnalyticSolve
import krylov.LinearAlgebra.MatrixAsymptotics

/-!
Article: main_krylov, lem:U and lem:projected-residual, spectral matrix regularity.
Use: pass genuine analytic entry formulas to actual spectral-norm matrix
functions through the existing continuous finite coordinate equivalence.
Source: the proved matrixEntryEquiv and mathlib's analytic linear-map and finite-product calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n p : ℕ}

/-- Entrywise genuine matrix analyticity gives genuine matrix analyticity in the source's spectral norm.
Use: first-order model errors and inverse bounds retain the actual operator norm.
Article: main_krylov, lem:U and lem:projected-residual.
Proof: assemble the finite entry vector analytically and apply the actual
continuous linear inverse coordinate equivalence into spectral-norm matrices. -/
theorem analytic_spectral_matrix (C : X → Matrix (Fin n) (Fin p) ℝ) (x : X)
    (hC : ∀ i j, AnalyticAt ℝ (fun z => C z i j) x) : AnalyticAt ℝ C x := by
  have he : AnalyticAt ℝ (fun z (ij : Fin n × Fin p) => C z ij.1 ij.2) x :=
    AnalyticAt.pi (fun ij => hC ij.1 ij.2)
  exact ((matrixEntryEquiv n p).symm.toContinuousLinearMap.analyticAt _).comp he

/-- Genuine finite inverse-entry regularity gives actual spectral-norm inverse regularity at the real determinant domain.
Use: actual normalized models have proved locally bounded genuine inverse norms.
Article: main_krylov, lem:projected-residual, actual inverse conditioning near a reference.
Proof: the proved analytic adjugate/determinant entries assemble through the genuine spectral coordinate equivalence. -/
theorem analytic_spectral_matrix_inv (C : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    (hC : ∀ i j, AnalyticAt ℝ (fun z => C z i j) x) (hu : (C x).det≠0) :
    AnalyticAt ℝ (fun z => (C z)⁻¹) x :=
  analytic_spectral_matrix _ x (analytic_matrix_inv C x hC hu)

end
end krylov.Stability
