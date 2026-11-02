import krylov.Methods.DeferredPrefix
import krylov.Stability.FCDomains

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), true last deferred model neighborhood.
Use: derive the actual final deferred conjugacy inverse domain near a
real positive active quadratic reference, without assuming a model domain.
Source: genuine identical pre-final FC history, true unused correction
oracle invariance and the proved actual open FC model domains.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine final deferred observed full conjugacy model is nonsingular on an actual neighborhood of every true active positive quadratic reference path.
Use: The genuine final deferred observed full conjugacy model is nonsingular on an actual neighborhood of every true active positive quadratic reference path.
Article: main_krylov, apB:lem:mu(d), true last deferred model neighborhood.
Proof: The real pre-final deferred history equals genuine FC and is independent of unused actual correction oracles. Transfer the proved true FC inverse neighborhood through the genuine complete-history determinant function. -/
theorem deferred_last_model_domain (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (a : ℝ)
    (hA : ∀ i, AnalyticAt ℝ (fun t => A t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (hpre : ∀ i<k+1, CG.gradient Q g i≠0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (methodRun (deferredMethod fullMemory (k+1) a) (A t) (B t) g k)))
      (windowSteps (selectedWindow fullMemory (methodRun (deferredMethod fullMemory (k+1) a) (A t) (B t) g k)))).det := by
  -- Reuse the genuine open FC inverse domain on the actual identical earlier complete history.
  have hdom := quadraticFC_domains A (fun _ => g) 0 hA analyticAt_const Q hA0 hQ hpos (k+1) hpre
  filter_upwards [hdom] with t ht
  have he : methodRun (deferredMethod fullMemory (k+1) a) (A t) (B t) g k=
      fcHistory fullMemory (A t) g k :=
    (deferredMethod_run_before fullMemory (k+1) a (A t) (B t) g k (by omega)).trans
      (correctionFree_run_independent (fcMethod fullMemory) (Variation.fcMethod_correctionFree fullMemory) (A t) (B t) (A t) g k)
  have hd := congrArg (fun H : History E =>
    (crossGram (windowImages (selectedWindow fullMemory H)) (windowSteps (selectedWindow fullMemory H))).det) he
  rw [hd]
  exact (ht k (by omega)).1
end
end krylov.Envelope
