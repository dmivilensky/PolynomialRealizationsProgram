import krylov.Methods.ProbedModelBasis

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(a), genuine final full-model reference domains.
Use: establish true quadratic final-gradient orthogonality and the actual
positive observed full model for every globally CG-consistent raw policy.
Source: proved actual CG step identities, nonstagnating CG conjugacy
and genuine positive quadratic Gram matrices.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full current-direction and old-step basis is orthogonal to the genuine final quadratic CG gradient.
Use: The actual full current-direction and old-step basis is orthogonal to the genuine final quadratic CG gradient.
Article: main_krylov, apB:lem:mu(a), genuine final full-model reference domains.
Proof: Identify each genuine current raw direction with a positive CG multiple and every actual old recorded step with its true CG step; apply real CG orthogonality. -/
theorem quadratic_stepBasis_coordinates_final (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+1, CG.gradient Q g i≠0) :
    coordinates (probedStepBasis m (fun _ => Q) (fun _ => Q) g k) (CG.gradient Q g (k+1))=0 := by
  -- True current direction scaling and exact old recorded CG steps share the same genuine final orthogonality.
  have hk := CG.invariant Q hQ hpos g (k+1) hpre
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change inner ℝ (m.direction (methodRun m (fun _ => Q) (fun _ => Q) g k)) (CG.gradient Q g (k+1))=0
    obtain ⟨c,_,hd,_⟩ := hm Q hQ hpos g k
    rw [hd,real_inner_smul_left,hk.old_direction k (by omega),mul_zero]
  · change inner ℝ (probedStep m (fun _ => Q) (fun _ => Q) g (k-1-j.val)) (CG.gradient Q g (k+1))=0
    rw [quadratic_probedStep_eq_cg m hm Q hQ hpos,referenceStep,real_inner_smul_left,hk.old_direction _ (by omega),mul_zero]

/-- The genuine full observed latest-model matrix is positive definite on every true active globally CG-consistent prefix.
Use: The genuine full observed latest-model matrix is positive definite on every true active globally CG-consistent prefix.
Article: main_krylov, apB:lem:mu(a), genuine final full-model reference domains.
Proof: Every actual observed image is the quadratic image of its genuine step; the real independent full step family therefore has a strictly positive operator Gram. -/
theorem quadratic_probedModel_posDef (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+1, CG.gradient Q g i≠0) :
    (pairModel (probedStepBasis m (fun _ => Q) (fun _ => Q) g k)
      (probedImageBasis m (fun _ => Q) (fun _ => Q) g k)).PosDef := by
  rw [quadratic_imageBasis,pairModel_quadratic _ Q hQ]
  have he : correctionCompression (probedStepBasis m (fun _ => Q) (fun _ => Q) g k) Q=
      crossGram (fun i => Q (probedStepBasis m (fun _ => Q) (fun _ => Q) g k i))
        (probedStepBasis m (fun _ => Q) (fun _ => Q) g k) := by
    ext i j
    exact (hQ _ _).symm
  rw [he]
  exact operatorGram_posDef Q hQ hpos (probedStepBasis_independent m hm Q hQ hpos g k (fun i hi => hpre i (by omega)))
end
end krylov.Methods
