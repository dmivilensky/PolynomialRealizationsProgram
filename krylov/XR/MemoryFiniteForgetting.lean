import krylov.XR.MemoryForgettingStep

/-!
Article: main_krylov, proof of thm:grow, actual finite forgetting theorem.
Use: after all newly observed segments are genuinely local, the real XR
run forgets every older segment in at most n+1 accepted outer iterations.
The proof includes its rejected probe, conditional curvature insertion,
chronological suffix cleanup and anchor transport. Source: the derived
strict bad-prefix potential decrease, not an assumed memory-age field.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real chronological suffix/probe executor finitely forgets all
old observations once its new accepted and optional probe data are good.
Only properties of actual newly evaluated segments are inputs here. -/
theorem run_finite_forgetting (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (bound : ℕ)
    (hdrop : ∀ S : State E, ∃ o, (model S).pairs = S.pairs.drop o)
    (hmodel : ∀ S : State E, (model S).pairs.length ≤ bound)
    (f : E → ℝ) (G : E → E) (S₀ : State E) (h₀ : S₀.pairs.length ≤ bound + 1)
    (Q : PairObservation E → Prop) (htransport : ∀ a u, Q (a.transport u) ↔ Q a)
    (K : ℕ)
    (hnew : ∀ k, K ≤ k →
      let S := run P dimension model f G S₀ k
      let R := outerSearch model f G P.armijo S
      S.gradient ≠ 0 ∧ Q (observedTrialPair f G S ((model S).safeDirection S)) ∧
        Q (observedTrialPair f G S (R.length • R.direction)) ∧
          positivePair (observedTrialPair f G S (R.length • R.direction))) :
    ∀ k, K + (bound + 1) ≤ k →
      ∀ a ∈ (run P dimension model f G S₀ k).pairs, Q a := by
  let states := run P dimension model f G S₀
  let bad := fun k => firstGoodSuffix Q (states k).pairs
  let potential := fun k => forgettingPotential (bound + 1) Q (states k).pairs
  have hlen k : (states k).pairs.length ≤ bound + 1 := by
    induction k with
    | zero => exact h₀
    | succ k ih => exact outerAdvance_pairs_length_le P dimension model bound hmodel f G _ ih
  have hstep k (hk : K ≤ k) : bad (k + 1) ≤ bad k ∧
      (bad (k + 1) ≠ 0 → potential (k + 1) + 1 ≤ potential k) := by
    have hn := hnew k hk
    exact outerAdvance_forgetting P dimension model bound hdrop hmodel f G (states k) hn.1
      Q (hlen k) htransport hn.2.1 hn.2.2.1 hn.2.2.2
  have hpotential : potential K ≤ bound + 1 :=
    forgettingPotential_le_capacity _ Q (states K).pairs (hlen K)
  have hind j : bad (K + j) = 0 ∨ potential (K + j) + j ≤ potential K := by
    induction j with
    | zero => right; simp only [Nat.add_zero, le_refl]
    | succ j ih =>
      have hs := hstep (K + j) (by omega)
      rcases ih with hz | hp
      · left
        have he : K + (j + 1) = K + j + 1 := by omega
        rw [he]
        omega
      · by_cases hz : bad (K + (j + 1)) = 0
        · exact Or.inl hz
        · right
          have hn := hs.2 (by simpa only [Nat.add_assoc] using hz)
          have he : K + (j + 1) = K + j + 1 := by omega
          rw [he]
          omega
  have hbase : bad (K + (bound + 1)) = 0 := by
    rcases hind (bound + 1) with hz | hp
    · exact hz
    · have hbadle : bad (K + (bound + 1)) ≤ potential (K + (bound + 1)) := by
        dsimp only [bad, potential, forgettingPotential]
        omega
      omega
  have hstay j : bad (K + (bound + 1) + j) = 0 := by
    induction j with
    | zero => simpa only [Nat.add_zero] using hbase
    | succ j ih =>
      have hs := (hstep (K + (bound + 1) + j) (by omega)).1
      have hz : bad (K + (bound + 1) + j + 1) = 0 := by omega
      simpa only [Nat.add_assoc] using hz
  intro k hk
  have he : K + (bound + 1) + (k - (K + (bound + 1))) = k := by omega
  have hb := hstay (k - (K + (bound + 1)))
  rw [he] at hb
  exact (firstGoodSuffix_eq_zero_iff Q (states k).pairs).mp hb

end
end krylov.XR
