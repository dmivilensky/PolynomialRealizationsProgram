import krylov.XR.EuclideanProbeMemory
import krylov.XR.GrowthFullMemory
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

/-- With full capacity, no actual cleanup deletion means the sole probe
cannot reduce the number of pairs reaching the accepted search. -/
theorem euclideanOuterSearch_full_length_ge (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hcap : S.capacity = n)
    (hfirst : (euclideanAlgorithmModel P S).pairs = incomingWindow S)
    (hsecond : ¬Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 →
      (euclideanAlgorithmModel P (firstProbeState (euclideanAlgorithmModel P) f G S)).pairs =
        incomingWindow (firstProbeState (euclideanAlgorithmModel P) f G S)) :
    min n S.pairs.length ≤ (outerSearch (euclideanAlgorithmModel P) f G P.armijo S).pairs.length := by
  classical
  let S₁ := firstProbeState (euclideanAlgorithmModel P) f G S
  have hcount : (euclideanAlgorithmModel P S).pairs.length = min n S.pairs.length := by
    rw [hfirst]
    simp only [incomingWindow, retainNewest_length, hcap, min_self]
  unfold outerSearch
  dsimp only
  split
  · exact hcount.ge
  · rename_i hreject
    change min n S.pairs.length ≤ (euclideanAlgorithmModel P S₁).pairs.length
    rw [hsecond hreject]
    have hlen : (euclideanAlgorithmModel P S).pairs.length ≤ S₁.pairs.length :=
      appendPositive_length_ge _ _
    simp only [incomingWindow, retainNewest_length]
    change min n S.pairs.length ≤ min (min S.capacity n) S₁.pairs.length
    rw [hcap, min_self]
    omega

/-- The actual accepted positive observation raises the retained count,
including when the first probe was rejected and recomputed. -/
theorem euclideanOuterAdvance_full_length_ge (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hg : S.gradient ≠ 0) (hcap : S.capacity = n)
    (hfirst : (euclideanAlgorithmModel P S).pairs = incomingWindow S)
    (hsecond : ¬Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 →
      (euclideanAlgorithmModel P (firstProbeState (euclideanAlgorithmModel P) f G S)).pairs =
        incomingWindow (firstProbeState (euclideanAlgorithmModel P) f G S))
    (hpositive : positivePair (observedTrialPair f G S
      ((outerSearch (euclideanAlgorithmModel P) f G P.armijo S).length •
        (outerSearch (euclideanAlgorithmModel P) f G P.armijo S).direction))) :
    min n S.pairs.length + 1 ≤ (outerAdvance P n (euclideanAlgorithmModel P) f G S).pairs.length := by
  classical
  have hlen := euclideanOuterSearch_full_length_ge P f G S hcap hfirst hsecond
  simp only [outerAdvance, ite_eq_right hg]
  rw [List.length_map, appendPositive, ite_eq_left hpositive, List.length_append, List.length_singleton]
  omega


end
end krylov.XR
