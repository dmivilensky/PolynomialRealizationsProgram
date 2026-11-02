import krylov.Methods.OneGradientCoordinates
import krylov.Stability.ContDiffSolve

/-!
Article: main_krylov, lem:U(d), primitive smooth trial rules in true observed coordinates.
Use: convert the source's C² observed-data trial hypothesis into genuine
regularity of the trial selected by the actual one-gradient executor.
Source: exact finite real-history charts and standard C^r composition.
No trajectory or trial-along-trajectory smoothness is assumed.
-/

namespace krylov.Stability
noncomputable section
open krylov.Methods
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The primitive data-only trial rule in fixed finite observed-vector coordinates.
Use: C² smoothness is imposed on this actual coefficient function before any trajectory is differentiated.
Article: main_krylov, lem:U(d), C² positive XRFC trial rule. -/
def trialCoordinate (trial : History E → ℝ) (k : ℕ) : E × (Fin k → E) × (Fin k → E) → ℝ :=
  fun data => trial (oneGradientHistoryChart data)

/-- The genuine finite initial/step/returned-gradient data of an actual one-gradient prefix.
Use: the trial-coordinate hypothesis is evaluated at real observed reference data.
Article: main_krylov, def:classes(M₁) and lem:U(d). -/
def oneGradientData (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    E × (Fin k → E) × (Fin k → E) :=
  (g,(fun i => oneGradientStep m A g (k-1-i.val)),
    (fun i => oneGradientGradient m A g (k-i.val)))

/-- A primitive C^r observed-data trial rule yields a genuine C^r trial on the actual smooth observed prefix.
Use: real XRFC regularity assumes smooth primitive coefficient rules, not the desired smoothness of an executed policy.
Article: main_krylov, lem:U(d), actual data-dependent trial regularity.
Proof: the exact real-history chart identifies the actual trial with its
primitive finite coefficient function. Real past step and returned-gradient
regularity gives a C^r finite data tuple, which is composed with that true rule. -/
theorem actual_trial_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ) (m : OneGradientMethod E)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ)
    (hg : ContDiffAt ℝ r g x)
    (hs : ∀ i<k, ContDiffAt ℝ r (fun p => oneGradientStep m (A p) (g p) i) x)
    (hG : ∀ i≤k, ContDiffAt ℝ r (fun p => oneGradientGradient m (A p) (g p) i) x)
    (ht : ContDiffAt ℝ r (trialCoordinate trial k) (oneGradientData m (A x) (g x) k)) :
    ContDiffAt ℝ r (fun p => trial (oneGradientRun m (A p) (g p) k)) x := by
  -- Only already observed vectors enter this data tuple; no unknown next operator image is used.
  have hS : ContDiffAt ℝ r (fun p (i : Fin k) => oneGradientStep m (A p) (g p) (k-1-i.val)) x :=
    contDiffAt_pi.mpr fun i => hs _ (by omega)
  have hGs : ContDiffAt ℝ r (fun p (i : Fin k) => oneGradientGradient m (A p) (g p) (k-i.val)) x :=
    contDiffAt_pi.mpr fun i => hG _ (by omega)
  have hd : ContDiffAt ℝ r (fun p => oneGradientData m (A p) (g p) k) x :=
    hg.prodMk (hS.prodMk hGs)
  have hc := ht.comp (g := trialCoordinate trial k) (f := fun p => oneGradientData m (A p) (g p) k) x hd
  apply hc.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [trialCoordinate,oneGradientData]
  rw [oneGradientRun_chart m (A p) (g p) k]
  rfl

end
end krylov.Stability
