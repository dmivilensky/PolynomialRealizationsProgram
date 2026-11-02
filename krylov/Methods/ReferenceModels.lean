import krylov.Methods.QuadraticCycles

/-!
Article: main_krylov, lem:consistent(a), genuine quadratic model domains.
Use: establish positive definiteness of the actual retained and augmented
models and verify the observed gate, before invoking any inverse solve.
Source: positivity of actual operator Gram matrices and actual CG conjugacy.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual suffix of nonstagnating reference steps is independent for every retained length.
Use: the computed quadratic window models are nonsingular without an assumed reference-model field.
Article: main_krylov, lem:consistent(a), retained model domain.
Proof: the actual age map is injective and lies in the earlier nonzero prefix,
so the already proved selected-reference independence theorem applies. -/
theorem retainedSteps_independent (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) :
    LinearIndependent ℝ (windowSteps ((referencePairs Q g k).take m)) := by
  -- The suffix is selected from the true finite reference, with no lower bound on its step energies.
  let W := (referencePairs Q g k).take m
  have hi (i : Fin W.length) : i.val<k := by
    have h := i.isLt
    simp only [W, List.length_take, referencePairs_length] at h
    omega
  have hs : windowSteps W=fun i => referenceStep Q g (k-1-i.val) := by
    funext i
    exact congrArg Prod.fst (retained_pair Q g k m i)
  rw [hs]
  apply reference_window_independent Q hQ hpos g k hg
  · intro i j hij
    change k-1-i.val=k-1-j.val at hij
    apply Fin.ext
    have := hi i
    have := hi j
    omega
  · intro i; have := hi i; omega

/-- Actual retained quadratic images are precisely the true operator images of their stored steps.
Use: the concrete newest-first latest model is a true operator Gram matrix.
Article: main_krylov, lem:consistent(a), Y=AS.
Proof: both components of each actual reference pair have the proved chronological description. -/
theorem retainedImages_quadratic (Q : E →L[ℝ] E) (g : E) (k m : ℕ)
    (i : Fin ((referencePairs Q g k).take m).length) :
    windowImages ((referencePairs Q g k).take m) i=Q (windowSteps ((referencePairs Q g k).take m) i) := by
  have hp := retained_pair Q g k m i
  change (((referencePairs Q g k).take m).get i).2=Q (((referencePairs Q g k).take m).get i).1
  rw [hp]

/-- The actual retained quadratic latest-information model is positive definite.
Use: justifies every retained quadratic model inverse in FC/RFC/XRFC.
Article: main_krylov, lem:consistent(a), T̄=SᵀAS.
Proof: the actual latest model is its genuine symmetric operator Gram matrix,
and actual retained CG steps are independently proved linearly independent. -/
theorem retainedModel_posDef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) :
    (windowModel ((referencePairs Q g k).take m)).PosDef := by
  rw [windowModel_quadratic _ Q hQ (retainedImages_quadratic Q g k m)]
  exact operatorGram_posDef Q hQ hpos (retainedSteps_independent Q hQ hpos g k m hg)

/-- The actual retained quadratic conjugacy matrix is positive definite.
Use: the FC coefficient inverse is justified on its actual reference data.
Article: main_krylov, lem:consistent(a), YᵀS=SᵀAS.
Proof: actual images are operator images, and the retained actual steps are independent. -/
theorem retainedConjugacy_posDef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) :
    (crossGram (windowImages ((referencePairs Q g k).take m))
      (windowSteps ((referencePairs Q g k).take m))).PosDef := by
  have hy : windowImages ((referencePairs Q g k).take m)=
      fun i => Q (windowSteps ((referencePairs Q g k).take m) i) :=
    funext (retainedImages_quadratic Q g k m)
  rw [hy]
  exact operatorGram_posDef Q hQ hpos (retainedSteps_independent Q hQ hpos g k m hg)

omit [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
/-- Prepending an actual pair prepends its actual step to the finite window family.
Use: augmented RFC model independence uses the exact stored current direction.
Article: main_krylov, alg:fc, U=[S,d], newest-first order.
Proof: evaluate the actual head and every actual successor index. -/
theorem windowSteps_cons (p : E × E) (W : List (E × E)) :
    windowSteps (p::W)=Fin.cons p.1 (windowSteps W) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The actual RFC augmented reference steps are independent before the current search is exhausted.
Use: establishes the genuine augmented correction-model inverse rather than only totalized zero coefficients.
Article: main_krylov, lem:consistent(a), augmented U=[S,d].
Proof: the current CG direction has positive self-curvature and zero pairing
with every old step; it cannot lie in their span, so prepend it to the actual independent retained family. -/
theorem augmentedSteps_independent (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) :
    LinearIndependent ℝ (windowSteps ((CG.direction Q g k,Q (CG.direction Q g k))::
      (referencePairs Q g k).take m)) := by
  -- A genuine positive current curvature separates the current direction from the entire actual old span.
  let W := (referencePairs Q g k).take m
  have hk := CG.invariant Q hQ hpos g k (fun i hi => hg i hi.le)
  have hd := (CG.invariant_line_pos Q hpos g k hk (hg k le_rfl)).1
  rw [windowSteps_cons]
  apply (retainedSteps_independent Q hQ hpos g k m (fun i hi => hg i hi.le)).finCons
  intro hc
  have hle : Submodule.span ℝ (Set.range (windowSteps W))≤(innerSL ℝ (Q (CG.direction Q g k))).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hp := congrArg Prod.fst (retained_pair Q g k m i)
    have hi : i.val<k := by
      have h := i.isLt
      simp only [W, List.length_take, referencePairs_length] at h
      omega
    change inner ℝ (Q (CG.direction Q g k)) (windowSteps W i)=0
    rw [show windowSteps W i=referenceStep Q g (k-1-i.val) from hp, real_inner_comm,
      referenceStep, real_inner_smul_left, hk.conjugate _ k (by omega) le_rfl, mul_zero]
  have he := hle hc
  change inner ℝ (Q (CG.direction Q g k)) (CG.direction Q g k)=0 at he
  rw [real_inner_comm] at he
  exact (hpos _ hd).ne' he

/-- The actual RFC augmented quadratic latest model is positive definite.
Use: every repeated quadratic correction uses a genuine nonsingular physical model.
Article: main_krylov, lem:consistent(a), H=UᵀAU.
Proof: identify each actual observed image and apply positive operator Gram
positivity to the proved actual independent augmented family. -/
theorem augmentedModel_posDef (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) :
    (windowModel ((CG.direction Q g k,Q (CG.direction Q g k))::
      (referencePairs Q g k).take m)).PosDef := by
  rw [windowModel_quadratic _ Q hQ (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact retainedImages_quadratic Q g k m j)]
  exact operatorGram_posDef Q hQ hpos (augmentedSteps_independent Q hQ hpos g k m hg)

end
end krylov.Methods
