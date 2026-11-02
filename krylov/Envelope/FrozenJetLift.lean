import krylov.Envelope.GradientJetLift
import krylov.Envelope.KrylovFlags
import krylov.Envelope.FrozenResponse
import krylov.Methods.WindowConsistency

/-!
Article: main_krylov, apB:lem:filtration, actual frozen CG jet lift.
Use: identify the true reference-gradient lift of each actual measured CG
step with its genuine frozen physical direction response, and control real
lift differences inside the actual reference Krylov flag.
Source: genuine measured CG direction recurrence, proved earlier-flag lift
compatibility and the actual physical frozen gradient/direction executor.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual measured-CG scalar direction recurrence applied to a supplied real gradient derivative sequence.
Use: The actual measured-CG scalar direction recurrence applied to a supplied real gradient derivative sequence.
Article: main_krylov, apB:lem:filtration, actual frozen CG jet lift.
Proof: Use the same genuine beta coefficients measured by the true reference run. -/
def gradientResponseDirection (Q : E →L[ℝ] E) (g : E) (δg : ℕ → E) : ℕ → E
  | 0 => -δg 0
  | k+1 => -δg (k+1)+CG.beta Q g k • gradientResponseDirection Q g δg k

/-- Lifting a genuine reference CG direction gives exactly its true frozen scalar direction response.
Use: Lifting a genuine reference CG direction gives exactly its true frozen scalar direction response.
Article: main_krylov, apB:lem:filtration, actual frozen CG jet lift.
Proof: The actual next CG recurrence is linear in its real residual and old direction. The true coordinate lift recovers each reference residual derivative and agrees on the actual earlier Krylov flag. -/
theorem gradientJetLift_cgDirection (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (δg : ℕ → E) (k : ℕ)
    (hpre : ∀ i ≤ k, CG.gradient Q g i≠0) :
    gradientJetLift Q g δg k (CG.direction Q g k)=gradientResponseDirection Q g δg k := by
  -- The actual old direction belongs to its true earlier Krylov flag, where the two genuine prefix lifts agree.
  induction k with
  | zero =>
    change gradientJetLift Q g δg 0 (-CG.gradient Q g 0)= -δg 0
    rw [map_neg,gradientJetLift_gradient Q hQ hpos g δg 0 hpre 0 le_rfl]
  | succ k ih =>
    change gradientJetLift Q g δg (k+1) (CG.direction Q g (k+1))=
      -δg (k+1)+CG.beta Q g k • gradientResponseDirection Q g δg k
    rw [CG.direction_succ,map_add,map_neg,map_smul,
      gradientJetLift_gradient Q hQ hpos g δg (k+1) hpre (k+1) le_rfl]
    have hmem := cgDirection_mem_krylov Q g k (fun i hi =>
      ((CG.invariant Q hQ hpos g (k+1) (fun j hj => hpre j (by omega))).lines_pos i hi).ne')
    rw [gradientJetLift_restrict Q hQ hpos g δg (k+1) k hpre (Nat.le_succ k) hmem,
      ih (fun i hi => hpre i (by omega))]

/-- The measured-CG scalar lift of the actual frozen gradient response is its genuine physical frozen direction.
Use: The measured-CG scalar lift of the actual frozen gradient response is its genuine physical frozen direction.
Article: main_krylov, apB:lem:filtration, actual frozen CG jet lift.
Proof: The actual recurrences and empty states coincide. -/
theorem gradientResponseDirection_frozen (Q : E →L[ℝ] E) (g : E) (ζ : ℕ → E) (k : ℕ) :
    gradientResponseDirection Q g (fun i => frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ i 0) k=
      frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ k 1 := by
  induction k with
  | zero => simp only [gradientResponseDirection,frozenResponse_zero,Pi.zero_apply,neg_zero]
  | succ k ih => rw [gradientResponseDirection,ih,frozenResponse_direction_succ]

/-- The true coordinate lift of an actual reference CG step is exactly its genuine frozen physical step.
Use: The true coordinate lift of an actual reference CG step is exactly its genuine frozen physical step.
Article: main_krylov, apB:lem:filtration, actual frozen CG jet lift.
Proof: Scale the real direction-lift identity by its actual measured line length and identify the genuine frozen direction. -/
theorem gradientJetLift_frozen_step (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (ζ : ℕ → E) (k : ℕ)
    (hpre : ∀ i ≤ k, CG.gradient Q g i≠0) :
    gradientJetLift Q g (fun i => frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ i 0) k (referenceStep Q g k)=
      CG.length Q g k • frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ k 1 := by
  rw [referenceStep,map_smul,gradientJetLift_cgDirection Q hQ hpos g _ k hpre,gradientResponseDirection_frozen]

/-- Differences of genuine reference-gradient lifts remain in every true subspace containing the actual input gradient-derivative differences.
Use: Differences of genuine reference-gradient lifts remain in every true subspace containing the actual input gradient-derivative differences.
Article: main_krylov, apB:lem:filtration, actual frozen CG jet lift.
Proof: The true fixed reference coordinates turn the lift difference into a finite sum of actual derivative differences with real scalar coefficients. -/
theorem gradientJetLift_sub_mem (Q : E →L[ℝ] E) (g : E) (δg δh : ℕ → E) (k : ℕ)
    (K : Submodule ℝ E) (hδ : ∀ i ≤ k, δg i-δh i∈K) (v : E) :
    gradientJetLift Q g δg k v-gradientJetLift Q g δh k v∈K := by
  change (∑ i∈Finset.range (k+1), _)-(∑ i∈Finset.range (k+1), _)∈K
  rw [← Finset.sum_sub_distrib]
  apply K.sum_mem
  intro i hi
  rw [← smul_sub]
  exact K.smul_mem _ (hδ i (by have := Finset.mem_range.mp hi;omega))
end
end krylov.Envelope
