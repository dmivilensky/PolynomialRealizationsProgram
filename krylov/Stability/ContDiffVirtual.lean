import krylov.Stability.ContDiffSolve
import krylov.Methods.VirtualCoordinates
import krylov.Methods.XRFC

/-!
Article: main_krylov, lem:U(d), genuine C^r virtual-launch block solves.
Use: propagate actual smooth observed data through the real latest-model
virtual correction, extrapolated gradient and subsequent conjugacy direction.
Source: the proved analytic primitive inverse solves composed with C^r data;
reference domains come from the already proved actual XRFC basis invariant.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual finite virtual correction, extrapolated gradient and direction are C^r in their genuine C^r observations at both true inverse domains.
Use: XRFC trial smoothness propagates through the actual virtual-launch block without an assumed regular trajectory.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: each actual latest-model entry is a smooth observed inner product;
its true model inverse gives smooth computed coefficients. Both physical
combinations are smooth, and the real nonsingular conjugacy solve applies to the actual extrapolated gradient. -/
theorem contDiff_virtualBlock {p : ℕ} {r : WithTop ℕ∞} (S Y : X → Fin p → E) (g : X → E) (x : X)
    (hS : ∀ i, ContDiffAt ℝ r (fun z => S z i) x)
    (hY : ∀ i, ContDiffAt ℝ r (fun z => Y z i) x) (hg : ContDiffAt ℝ r g x)
    (hM : (pairModel (S x) (Y x)).det≠0) (hC : (crossGram (Y x) (S x)).det≠0) :
    let w := fun z => modelCoefficients (S z) (pairModel (S z) (Y z)) (g z)
    let gv := fun z => g z+combine (Y z) (w z)
    ContDiffAt ℝ r (fun z => combine (S z) (w z)) x ∧
      ContDiffAt ℝ r gv x ∧ ContDiffAt ℝ r (fun z => conjugacyDirection (S z) (Y z) (gv z)) x := by
  -- The inverse hypotheses refer to the real two observed matrices; no output regularity is supplied.
  have hH (i j : Fin p) : ContDiffAt ℝ r (fun z => pairModel (S z) (Y z) i j) x :=
    (hS (max i j)).inner ℝ (hY (min i j))
  have hw := contDiff_modelCoefficients S (fun z => pairModel (S z) (Y z)) g x hS hH hg hM
  have hcorr := contDiff_combine S _ x hS hw
  have hgrad := hg.add (contDiff_combine Y _ x hY hw)
  exact ⟨hcorr,hgrad,contDiff_conjugacyDirection S Y _ x hS hY hgrad hC⟩

end
end krylov.Stability
