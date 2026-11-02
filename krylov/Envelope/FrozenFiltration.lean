import krylov.Envelope.FrozenJetLift

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, genuine finite filtered-displacement induction.
Use: convert actual gradient-jet balance and one-step observed-jet coherence
into the true frozen physical displacement congruence at every finite prefix.
The raw-policy observation induction supplying one-step coherence is a separate
bridge; this reusable filtered induction assumes no trajectory expansion.
Source: actual measured CG jet lift, genuine frozen physical executor, true
Krylov flag growth and strong finite induction on the real horizon.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Genuine gradient balance and actual one-step observed-jet coherence force the true frozen displacement congruence on every reference prefix.
Use: Genuine gradient balance and actual one-step observed-jet coherence force the true frozen displacement congruence on every reference prefix.
Article: main_krylov, apB:lem:filtration, genuine finite filtered-displacement induction.
Proof: Strong finite induction compares actual and frozen gradient jets through the genuine reference operator. True Krylov flag growth controls each lifted gradient difference, the measured reference-step lift identifies the actual frozen step, and the genuine physical displacement sums preserve the filtered remainder. -/
theorem coherent_steps_frozen_filtration (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ k < N, CG.gradient Q g k≠0) (δs δg ζ : ℕ → E)
    (hgrad : ∀ k ≤ N, δg k=Q (∑ i∈Finset.range k, δs i)+∑ i∈Finset.range k, ζ (i+1))
    (hstep : ∀ k < N, δs k-gradientJetLift Q g δg k (referenceStep Q g k)∈CG.krylovSpace Q g (k+1)) :
    ∀ k ≤ N, (∑ i∈Finset.range k, δs i)-
      frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ k∈CG.krylovSpace Q g k := by
  -- Use the genuine measured-coefficient physical executor as the comparison displacement.
  let ξ := frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ
  let F := fun i => frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ i 0
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero => change (0 : E)-0∈CG.krylovSpace Q g 0;simp only [sub_self];exact Submodule.zero_mem _
    | succ k =>
      have hprev : (∑ i∈Finset.range k, δs i)-ξ k∈CG.krylovSpace Q g k := ih k (Nat.lt_succ_self k) (by omega)
      -- Every actual gradient-jet difference comes from an earlier genuine displacement remainder through the true reference operator.
      have hδ : ∀ i ≤ k, δg i-F i∈CG.krylovSpace Q g (k+1) := by
        intro i hi
        have hXi : (∑ j∈Finset.range i, δs j)-ξ i∈CG.krylovSpace Q g i := ih i (by omega) (by omega)
        have hFi := frozen_gradient_displacement Q (CG.length Q g) (CG.beta Q g) ζ i
        change F i=Q (ξ i)+_ at hFi
        have hid : δg i-F i=Q ((∑ j∈Finset.range i, δs j)-ξ i) := by
          rw [hgrad i (by omega),hFi,map_sub]
          abel
        rw [hid]
        exact krylovSpace_mono Q g (by omega : i+1 ≤ k+1) (krylovSpace_operator Q g i hXi)
      have hL := gradientJetLift_sub_mem Q g δg F k (CG.krylovSpace Q g (k+1)) hδ (referenceStep Q g k)
      have hFs := gradientJetLift_frozen_step Q hQ hpos g ζ k (fun i hi => hpre i (by omega))
      change gradientJetLift Q g F k (referenceStep Q g k)=_ at hFs
      -- The actual step coherence and proved measured frozen-step lift give the next genuine filtered step error.
      have hst : δs k-CG.length Q g k • frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ k 1∈
          CG.krylovSpace Q g (k+1) := by
        rw [← hFs]
        convert (CG.krylovSpace Q g (k+1)).add_mem (hstep k (by omega)) hL using 1
        abel
      have hξ : ξ (k+1)=ξ k+CG.length Q g k • frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ k 1 :=
        Finset.sum_range_succ _ k
      change (∑ i∈Finset.range (k+1), δs i)-ξ (k+1)∈CG.krylovSpace Q g (k+1)
      rw [Finset.sum_range_succ,hξ]
      convert (CG.krylovSpace Q g (k+1)).add_mem (krylovSpace_mono Q g (Nat.le_succ k) hprev) hst using 1
      abel
end
end krylov.Envelope
