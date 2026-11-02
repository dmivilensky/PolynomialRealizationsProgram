import krylov.Stability.AnalyticMatrix
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch and lem:U, primitive C-r spectral matrix calculus.
Use: derive actual observed full-model and oblique-flag regularity from real
entry data at genuine inverse domains, for arbitrary smooth trial policies.
Source: the reused matrixEntryEquiv and standard smooth inversion on the
unit group of the original finite-dimensional real normed matrix algebra.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n p : ℕ} {r : WithTop ℕ∞}

/-- Actual C-r matrix entries assemble to C-r matrices in the original spectral norm.
Use: no entrywise perturbation norm enters the physical regularity theorem.
Article: main_krylov, prop:launch; lem:U.
Proof: assemble genuine finite entry coordinates and compose the existing
continuous linear inverse coordinate equivalence into spectral-norm matrices. -/
theorem contDiff_spectral_matrix (C : X → Matrix (Fin n) (Fin p) ℝ) (x : X)
    (hC : ∀ i j,ContDiffAt ℝ r (fun z => C z i j) x) : ContDiffAt ℝ r C x := by
  have he : ContDiffAt ℝ r (fun z (ij : Fin n×Fin p) => C z ij.1 ij.2) x :=
    contDiffAt_pi.mpr (fun ij => hC ij.1 ij.2)
  exact (matrixEntryEquiv n p).symm.toContinuousLinearMap.contDiff.contDiffAt.comp x he

/-- Genuine C-r matrix curves have C-r actual inverses on their true determinant domain.
Use: the real oblique flags and full observed models inherit primitive regularity.
Article: main_krylov, prop:launch; lem:U.
Proof: the actual matrix is a unit, so standard normed-algebra smooth inversion
composes with its primitive C-r curve; ringInverse is the genuine matrix inverse. -/
theorem contDiff_spectral_inverse (C : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    (hC : ContDiffAt ℝ r C x) (hu : IsUnit (C x).det) :
    ContDiffAt ℝ r (fun z => (C z)⁻¹) x := by
  have hunit : IsUnit (C x) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
  have hi := contDiffAt_ringInverse (n := r) ℝ hunit.unit
  simpa only [Function.comp_def,Matrix.nonsing_inv_eq_ringInverse] using hi.comp x hC

end
end krylov.Stability
