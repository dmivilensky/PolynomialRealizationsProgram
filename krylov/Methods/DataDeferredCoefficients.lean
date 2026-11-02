import krylov.Methods.DeferredCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs and s3:def:DC, genuine data-dependent estimate calculus.
Use: extend the already proved native constant-estimate coefficient calculus
to the actual original smooth observed estimate, without assuming a smooth
executed trajectory or a prescribed cancellation response.
Source: genuine native conjugacy/model coefficient splitting, standard smooth
scalar inversion on the nonzero actual estimate and true finite combination.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Stability
variable {E X ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι] [DecidableEq ι]

/-- Actual native tilted coefficients are C-r for a genuine C-r nonzero
data-dependent estimate on their true observed cross-Gram domain.
Use: arbitrary primitive smooth DC-slide and final deferred policies use the
same real inverse solve as their original implementation.
Article: main_krylov, thm:dcs(c) and s3:def:DC.
Proof: reuse the exact native coefficient split into actual conjugacy and
model solves; compose their proved primitive regularity with the genuine
smooth inverse of the original scalar estimate. -/
theorem contDiff_dataDeferredCoefficients {r : WithTop ℕ∞}
    (s y : X → ι → E) (g : X → E) (a : X → ℝ) (x : X)
    (hs : ∀ i,ContDiffAt ℝ r (fun p => s p i) x)
    (hy : ∀ i,ContDiffAt ℝ r (fun p => y p i) x) (hg : ContDiffAt ℝ r g x)
    (ha : ContDiffAt ℝ r a x) (ha0 : a x≠0)
    (hdet : (crossGram (y x) (s x)).det≠0) (i : ι) :
    ContDiffAt ℝ r (fun p => deferredCoefficients (s p) (y p) (g p) (a p) i) x := by
  simp_rw [deferredCoefficients_split]
  exact (contDiff_conjugacyCoefficients s y g x hs hy hg hdet i).add
    ((ha.inv ha0).mul (contDiff_modelCoefficients s (fun p => crossGram (y p) (s p)) g x hs
      (fun i j => (hy i).inner ℝ (hs j)) hg hdet i))

/-- The actual tilted physical direction inherits exactly the primitive
C-r regularity of its true observed data and nonzero data-only estimate.
Use: real DC-slide direction smoothness is derived from its native finite solve.
Article: main_krylov, thm:dcs(c) and s3:def:DC.
Proof: synthesize the genuine smooth native coefficients with the actual
stored observed vectors and add the real negative current gradient. -/
theorem contDiff_dataDeferredDirection {r : WithTop ℕ∞}
    (s y : X → ι → E) (g : X → E) (a : X → ℝ) (x : X)
    (hs : ∀ i,ContDiffAt ℝ r (fun p => s p i) x)
    (hy : ∀ i,ContDiffAt ℝ r (fun p => y p i) x) (hg : ContDiffAt ℝ r g x)
    (ha : ContDiffAt ℝ r a x) (ha0 : a x≠0)
    (hdet : (crossGram (y x) (s x)).det≠0) :
    ContDiffAt ℝ r (fun p => deferredDirection (s p) (y p) (g p) (a p)) x :=
  hg.neg.add (contDiff_combine s _ x hs
    (contDiff_dataDeferredCoefficients s y g a x hs hy hg ha ha0 hdet))

end
end krylov.Methods
