import krylov.Methods.DeferredDirection
import krylov.Stability.ContDiffSolve

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual primitive deferred coefficients.
Use: derive the genuine tilted direction coefficients from existing real
conjugacy/model solves and prove actual primitive finite-order regularity.
Source: proved genuine observed inverse-model calculus and real finite
matrix/vector linearity.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine deferred coefficients split into the actual conjugacy coefficients plus the real inverse-estimate model coefficients.
Use: The genuine deferred coefficients split into the actual conjugacy coefficients plus the real inverse-estimate model coefficients.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual primitive deferred coefficients.
Proof: Distribute the true observed inverse matrix over its actual two right-hand sides. -/
theorem deferredCoefficients_split (s y : ι → E) (g : E) (a : ℝ) :
    deferredCoefficients s y g a=conjugacyCoefficients s y g+
      a⁻¹ • modelCoefficients s (crossGram y s) g := by
  unfold deferredCoefficients conjugacyCoefficients modelCoefficients
  rw [Matrix.mulVec_sub,Matrix.mulVec_smul]
  module

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual deferred direction coefficients are C-r on their genuine observed cross-Gram inverse domain.
Use: The actual deferred direction coefficients are C-r on their genuine observed cross-Gram inverse domain.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual primitive deferred coefficients.
Proof: Reuse the true primitive conjugacy and model coefficient calculus and the genuine constant inverse estimate. -/
theorem contDiff_deferredCoefficients {r : WithTop ℕ∞} (s y : X → ι → E) (g : X → E) (a : ℝ) (x : X)
    (hs : ∀ i, ContDiffAt ℝ r (fun p => s p i) x) (hy : ∀ i, ContDiffAt ℝ r (fun p => y p i) x)
    (hg : ContDiffAt ℝ r g x) (hdet : (crossGram (y x) (s x)).det≠0) (i : ι) :
    ContDiffAt ℝ r (fun p => deferredCoefficients (s p) (y p) (g p) a i) x := by
  simp_rw [deferredCoefficients_split]
  exact (contDiff_conjugacyCoefficients s y g x hs hy hg hdet i).add
    (contDiffAt_const.mul (contDiff_modelCoefficients s (fun p => crossGram (y p) (s p)) g x hs
      (fun i j => (hy i).inner ℝ (hs j)) hg hdet i))
end
end krylov.Methods
