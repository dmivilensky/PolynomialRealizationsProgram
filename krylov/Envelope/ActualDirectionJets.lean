import krylov.Methods.SmoothProbedDecisions
import krylov.Envelope.ObservedJets

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, actual raw direction first jets.
Use: propagate the true complete observed-history first-jet flag through
the actual direction decision of a genuinely smooth CG-consistent raw method.
Source: genuine primitive observed coefficient derivative closure and
proved actual local raw-policy decision equality.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true direction first jet chosen by a genuine smooth CG-consistent raw method preserves its actual complete observed-history jet flag.
Use: The true direction first jet chosen by a genuine smooth CG-consistent raw method preserves its actual complete observed-history jet flag.
Article: main_krylov, apB:lem:filtration, actual raw direction first jets.
Proof: Extract the real primitive direction coefficients at the actual raw history. Their genuine local finite-list decision preserves true coordinate jet coherence, and actual local direction equality transfers its real derivative to the raw policy. -/
theorem actual_direction_jet (m : ProbedMethod E) (hm : CGConsistent m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : ℝ → E) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0) (hg : ContDiffAt ℝ 2 g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<N, CG.gradient Q (g 0) i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q (g 0) N)
    (k : ℕ) (hk : k<N) (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (hH : JetListAt (jetSubspace K L) (fun t => (methodRun m (A t) (B t) (g t) k).observationList)) :
    (probedDirection m (A 0) (B 0) (g 0) k,
      deriv (fun t => probedDirection m (A t) (B t) (g t) k) 0)∈jetSubspace K L := by
  -- Apply primitive coefficient regularity at the true raw executed history, then transfer the actual local direction jet.
  obtain ⟨P,hcoef,he⟩ := smoothProbed_decisions m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk
  have hj := hH.decision K L P.directionRule _ hcoef.1
  have heq : (fun t => probedDirection m (A t) (B t) (g t) k)=ᶠ[𝓝 (0 : ℝ)]
      fun t => listDecision P.directionRule (methodRun m (A t) (B t) (g t) k).observationList :=
    he.mono fun _ ht => ht.1
  rw [show probedDirection m (A 0) (B 0) (g 0) k=_ from heq.self_of_nhds,heq.deriv_eq]
  exact hj
end
end krylov.Envelope
