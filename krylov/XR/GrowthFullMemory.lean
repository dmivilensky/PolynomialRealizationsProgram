import krylov.XR.LocalProbeMemory
import krylov.XR.MemoryStateInvariants

/-!
Article: main_krylov, thm:grow, full initial memory without G3.
Use: the actual first and optional second cleanup retain every incoming
observation on the local tail. The real accepted positive pair therefore
increases memory up to physical dimension even during backtracking and
while safeguard (G) is active. Source: literal suffix and insertion rules.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace
variable {n : ℕ}

/-- Optional positive insertion never decreases stored length. -/
theorem appendPositive_length_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : List (PairObservation E)) (a : PairObservation E) : W.length ≤ (appendPositive W a).length := by
  classical
  unfold appendPositive
  split <;> simp_all

/-- With full capacity, no actual cleanup deletion means the sole probe
cannot reduce the number of pairs reaching the accepted search. -/
theorem outerSearch_full_length_ge (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hcap : S.capacity = n)
    (hfirst : (algorithmModel P S).pairs = incomingWindow S)
    (hsecond : ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      (algorithmModel P (firstProbeState (algorithmModel P) f G S)).pairs =
        incomingWindow (firstProbeState (algorithmModel P) f G S)) :
    min n S.pairs.length ≤ (outerSearch (algorithmModel P) f G P.armijo S).pairs.length := by
  classical
  let S₁ := firstProbeState (algorithmModel P) f G S
  have hcount : (algorithmModel P S).pairs.length = min n S.pairs.length := by
    rw [hfirst]
    simp only [incomingWindow, retainNewest_length, hcap, min_self]
  unfold outerSearch
  dsimp only
  split
  · exact hcount.ge
  · rename_i hreject
    change min n S.pairs.length ≤ (algorithmModel P S₁).pairs.length
    rw [hsecond hreject]
    have hlen : (algorithmModel P S).pairs.length ≤ S₁.pairs.length :=
      appendPositive_length_ge _ _
    simp only [incomingWindow, retainNewest_length]
    change min n S.pairs.length ≤ min (min S.capacity n) S₁.pairs.length
    rw [hcap, min_self]
    omega

/-- The actual accepted positive observation raises the retained count,
including when the first probe was rejected and recomputed. -/
theorem outerAdvance_full_length_ge (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hg : S.gradient ≠ 0) (hcap : S.capacity = n)
    (hfirst : (algorithmModel P S).pairs = incomingWindow S)
    (hsecond : ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      (algorithmModel P (firstProbeState (algorithmModel P) f G S)).pairs =
        incomingWindow (firstProbeState (algorithmModel P) f G S))
    (hpositive : positivePair (observedTrialPair f G S
      ((outerSearch (algorithmModel P) f G P.armijo S).length •
        (outerSearch (algorithmModel P) f G P.armijo S).direction))) :
    min n S.pairs.length + 1 ≤ (outerAdvance P n (algorithmModel P) f G S).pairs.length := by
  classical
  have hlen := outerSearch_full_length_ge P f G S hcap hfirst hsecond
  simp only [outerAdvance, ite_eq_right hg]
  rw [List.length_map, appendPositive, ite_eq_left hpositive, List.length_append, List.length_singleton]
  omega

/-- A real positive-pair length recurrence fills physical dimension in at
most n further outer steps; this elementary lemma assumes no algorithmic
rate or successful test. -/
theorem length_fills_of_tail (len : ℕ → ℕ) (n K : ℕ)
    (hstep : ∀ k, K ≤ k → min n (len k) + 1 ≤ len (k + 1)) :
    ∀ k, K + n ≤ k → n ≤ len k := by
  have hfill (j : ℕ) : min j n ≤ len (K + j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hs := hstep (K + j) (by omega)
      rw [Nat.add_assoc] at hs
      omega
  intro k hk
  have h := hfill (k - K)
  rw [Nat.add_sub_of_le (by omega : K ≤ k)] at h
  omega

end
end krylov.XR
