import krylov.Methods.GenericReferencePairs

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), actual arbitrary-method augmented model domain.
Use: derive genuine full latest-model positivity for every actual globally
CG-consistent method and every true positive reference direction scale.
Source: standard positive operator Gram matrices (Meurant06), actual
CG augmented independence and genuine invertible coordinate rescaling.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine augmented current-direction and retained-step family remains actually linearly independent under every true nonzero current direction scale.
Use: The genuine augmented current-direction and retained-step family remains actually linearly independent under every true nonzero current direction scale.
Article: main_krylov, thm:select and apB:lem:mu(a), actual arbitrary-method augmented model domain.
Proof: Rescale only the actual current CG column by a genuine scalar unit, preserving all real old-step columns of the proved true independent augmented family. -/
theorem augmentedSteps_scaled_independent (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) (c : ℝ) (hc : c≠0) :
    LinearIndependent ℝ (windowSteps ((c • CG.direction Q g k,Q (c • CG.direction Q g k))::
      (referencePairs Q g k).take m)) := by
  -- Only the actual current augmented column is rescaled by a genuine nonzero scalar unit; every true earlier CG column is preserved.
  classical
  let W := (referencePairs Q g k).take m
  let v := windowSteps ((CG.direction Q g k,Q (CG.direction Q g k))::W)
  let w : Fin (W.length+1) → ℝˣ := fun i => if i=0 then Units.mk0 c hc else 1
  have hi : LinearIndependent ℝ v := augmentedSteps_independent Q hQ hpos g k m hg
  have he : w • v=windowSteps ((c • CG.direction Q g k,Q (c • CG.direction Q g k))::W) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [w,v,windowSteps]
    · simp [w,v,windowSteps,Fin.succ_ne_zero]
  rw [← he]
  exact hi.units_smul w

/-- The actual augmented latest-information model is positive definite for every genuine nonzero scaled CG current direction and true retained reference history.
Use: The actual augmented latest-information model is positive definite for every genuine nonzero scaled CG current direction and true retained reference history.
Article: main_krylov, thm:select and apB:lem:mu(a), actual arbitrary-method augmented model domain.
Proof: Identify the genuine observed model with the actual positive operator Gram matrix on the real independently scaled augmented family. -/
theorem augmentedModel_scaled_posDef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) (c : ℝ) (hc : c≠0) :
    (windowModel ((c • CG.direction Q g k,Q (c • CG.direction Q g k))::
      (referencePairs Q g k).take m)).PosDef := by
  rw [windowModel_quadratic _ Q hQ (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact retainedImages_quadratic Q g k m j)]
  exact operatorGram_posDef Q hQ hpos (augmentedSteps_scaled_independent Q hQ hpos g k m hg c hc)

/-- Every actual globally CG-consistent method has a genuine positive full augmented latest-information model on its true active quadratic reference transcript.
Use: Every actual globally CG-consistent method has a genuine positive full augmented latest-information model on its true active quadratic reference transcript.
Article: main_krylov, thm:select and apB:lem:mu(a), actual arbitrary-method augmented model domain.
Proof: Global real consistency supplies a positive current CG direction scale and the actual complete reference pair history. Apply the true scaled augmented positive-model theorem to the genuine full retained list. -/
theorem cgConsistent_augmented_model_posDef (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) :
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    (windowModel ((m.direction H,Q (m.direction H))::H.pairs)).PosDef := by
  dsimp only
  obtain ⟨c,hc,hd,_⟩ := hm Q hQ hpos g k
  rw [hd,cgConsistent_reference_pairs m hm Q hQ hpos g k]
  have htake : (referencePairs Q g k).take k=referencePairs Q g k :=
    List.take_of_length_le (by rw [referencePairs_length])
  have h := augmentedModel_scaled_posDef Q hQ hpos g k k hg c hc.ne'
  rw [htake] at h
  exact h

end
end krylov.Methods
