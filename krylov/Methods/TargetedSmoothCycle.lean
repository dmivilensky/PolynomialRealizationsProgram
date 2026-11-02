import krylov.Methods.TargetedCoefficientDomains
import krylov.Methods.ScaledReferenceModel

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine primitive smoothness of the targeted policy.
Use: derive actual C-r finite observed coefficient membership of the real reference-targeted method, independently of any global quadratic consistency assumption.
Source: genuine FC-prefix primitive compilation, true positive reference conjugacy and augmented models, and actual target-relative observed program domains.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual targeted policy has genuine primitive C-r coefficient charts on each true active reference cycle through its final correction.
Use: Every actual targeted policy has genuine primitive C-r coefficient charts on each true active reference cycle through its final correction.
Article: main_krylov, apB:prop:consist, genuine primitive smoothness of the targeted policy.
Proof: Its actual earlier complete histories are FC. Their true positive reference matrices derive every real inverse domain, and the genuine compiled policy agrees on the actual observed neighborhoods. -/
theorem targetedFinalMethod_smoothCycleAt (N : ℕ) (target : E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hpre : ∀ k<N,CG.gradient Q g k≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (targetedFinalMethod N target) r Q g N := by
  -- The actual target query occurs only at the end, so every genuine prefix uses the true FC primitive chart.
  let P := targetedCompiledPolicy N target (E := E)
  have hH (k : ℕ) (hk : k<N) : methodRun P.method (fun _ => Q) (fun _ => Q) g k=
      methodRun (fcMethod fullMemory) (fun _ => Q) (fun _ => Q) g k :=
    targetedCompiled_run_before N target _ _ g k hk
  have hs (k : ℕ) (hk : k<N) : (methodRun P.method (fun _ => Q) (fun _ => Q) g k).queryShape=
      List.replicate (methodRun P.method (fun _ => Q) (fun _ => Q) g k).records.length 0 := by
    rw [hH k hk,methodRun_length]
    exact methodRun_empty_corrections_shape (fcMethod fullMemory) (fun _ _ => rfl) _ _ g k
  -- Genuine positive CG reference models discharge all actual coefficient inverse domains before local policy transfer.
  refine ⟨P,?_,?_⟩
  · intro k hk
    apply targetedCompiled_coefficients_regular N target _ (hs k hk) r Q
    · have hW : selectedWindow fullMemory (methodRun P.method (fun _ => Q) (fun _ => Q) g k)=
          (referencePairs Q g k).take k := by
        rw [hH k hk]
        unfold selectedWindow
        rw [(fcMethod_static fullMemory Q hQ hpos g (fun _ _ hi => hi) k).2,methodRun_length]
        rfl
      rw [hW]
      exact (retainedConjugacy_posDef Q hQ hpos g k k (fun i hi => hpre i (hi.trans hk))).det_pos.ne'
    · rw [hH k hk,selectedWindow_full]
      exact (cgConsistent_augmented_model_posDef (fcMethod fullMemory) fullFC_consistent Q hQ hpos g k
        (fun i hi => hpre i (by omega))).det_pos.ne'
  · intro k hk
    exact targetedCompiled_local N target _ _ (hs k hk)
end
end krylov.Methods
