import krylov.XR.LocalRitzBounds
import krylov.XR.XRFCReplay

/-!
Article: main_krylov, proof of thm:XR, actual running Ritz bounds.
Use: propagate a true bound for the observed Ritz extrema through both
ModelSteps of the literal one-probe executor. The rejected probe updates
the running bound before the second solve; this intermediate update is
included explicitly. Source: the actual max update in alg:xr.
-/

namespace krylov.XR
noncomputable section
open Matrix Set Filter Topology krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}

/-- The current upper spectral estimate; zero is used only for unset data. -/
def boundsUpper (b : SpectralBounds) : ℝ := (b.map Prod.snd).getD 0

/-- A bound on the actually computed Ritz contribution at this ModelStep. -/
def ModelRitzBound (P : Parameters) (C : ℝ) (S : State (EuclideanSpace ℝ (Fin n))) : Prop :=
  0 < (algorithmModel P S).pairs.length →
    P.inflation * sSup (observedRayleighValues (algorithmModel P S).pairs) ≤ C

theorem algorithmModel_boundsUpper_le (P : Parameters) (C : ℝ) (_hC : 0 ≤ C)
    (S : State (EuclideanSpace ℝ (Fin n))) (hR : ModelRitzBound P C S) :
    boundsUpper (algorithmModel P S).bounds ≤ max (boundsUpper S.bounds) C := by
  classical
  rw [algorithmModel_bounds]
  by_cases hz : (algorithmModel P S).pairs.length = 0
  · simp only [hz, ite_true]
    exact le_max_left _ _
  · simp only [hz, ite_false]
    have hh := hR (Nat.pos_of_ne_zero hz)
    cases hb : S.bounds with
    | none =>
      simp only [updateBounds, boundsUpper, Option.map_some, Option.getD_some,
        Option.map_none, Option.getD_none]
      exact hh.trans (le_max_right _ _)
    | some b =>
      simp only [updateBounds, boundsUpper, Option.map_some, Option.getD_some]
      exact max_le_max_left _ hh

/-- Both actual ModelSteps preserve a uniform upper envelope, including
the running-bound update made after the first rejected probe. -/
theorem outerSearch_boundsUpper_le (P : Parameters) (C : ℝ) (hC : 0 ≤ C)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hR : ModelRitzBound P C S)
    (hprobe : ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      ModelRitzBound P C (firstProbeState (algorithmModel P) f G S)) :
    boundsUpper (outerSearch (algorithmModel P) f G P.armijo S).bounds ≤
      max (boundsUpper S.bounds) C := by
  classical
  unfold outerSearch
  dsimp only
  split
  · exact algorithmModel_boundsUpper_le P C hC S hR
  · rename_i hreject
    have hp := algorithmModel_boundsUpper_le P C hC
      (firstProbeState (algorithmModel P) f G S) (hprobe hreject)
    have hb : (firstProbeState (algorithmModel P) f G S).bounds = (algorithmModel P S).bounds := rfl
    rw [hb] at hp
    exact hp.trans (by
      rw [max_le_iff]
      exact ⟨algorithmModel_boundsUpper_le P C hC S hR,
        le_max_right _ _⟩)

/-- One real accepted/stopped update preserves the actual upper envelope. -/
theorem outerAdvance_boundsUpper_le (P : Parameters) (C : ℝ) (hC : 0 ≤ C)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hR : ModelRitzBound P C S)
    (hprobe : ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      ModelRitzBound P C (firstProbeState (algorithmModel P) f G S)) :
    boundsUpper (outerAdvance P n (algorithmModel P) f G S).bounds ≤
      max (boundsUpper S.bounds) C := by
  classical
  unfold outerAdvance
  split
  · exact le_max_left _ _
  · exact outerSearch_boundsUpper_le P C hC f G S hR hprobe

/-- A uniform eventual envelope on actual observed Ritz contributions
bounds every subsequent actual running upper estimate. -/
theorem algorithmRun_boundsUpper_bounded (P : Parameters) (C : ℝ) (hC : 0 ≤ C)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (K : ℕ)
    (hR : ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ModelRitzBound P C S ∧
        (¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
          ModelRitzBound P C (firstProbeState (algorithmModel P) f G S))) :
    ∀ k, K ≤ k → boundsUpper (algorithmRun P f G x₀ bounds k).bounds ≤
      max (boundsUpper (algorithmRun P f G x₀ bounds K).bounds) C := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => exact le_max_left _ _
  | succ j ih =>
    have hh := hR (K+j) (by omega)
    have hs := outerAdvance_boundsUpper_le P C hC f G
      (algorithmRun P f G x₀ bounds (K+j)) hh.1 hh.2
    change boundsUpper (algorithmRun P f G x₀ bounds (K+j+1)).bounds ≤ _ at hs
    exact hs.trans (max_le ih (le_max_right _ _))

end
end krylov.XR
