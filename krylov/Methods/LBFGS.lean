import krylov.Methods.VirtualReference
import krylov.Methods.Classes
import krylov.Methods.ReferenceModels
import krylov.Methods.ExecutedProbed

/-!
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Use: implement the actual two-loop inverse-BFGS action with scalar initial
metric and real newest-first retained secant pairs; derive its actual
conjugate-reference action from the established physical FC block solve.
Source: classical BFGS inverse update and two-loop recursion, Dixon72a,
Dixon72b, Nazareth79 and KoldaEtAl98; reuse genuine reference CG geometry.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual two-loop inverse-BFGS action with a scalar initial metric and the supplied real newest-first secant history.
Use: The actual two-loop inverse-BFGS action with a scalar initial metric and the supplied real newest-first secant history.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: The reverse pass removes the current pair component before the genuine recursive older-pair action, and the forward pass applies its real secant correction. -/
def inverseBFGSApply (c : ℝ) : List (E × E) → E → E
  | [],v => c • v
  | (s,y)::W,v =>
      let ρ := (inner ℝ s y)⁻¹
      let a := ρ*inner ℝ s v
      let r := inverseBFGSApply c W (v-a • y)
      r+(a-ρ*inner ℝ y r) • s

/-- The real two-loop action stays in every true subspace containing its actual input and retained secant vectors.
Use: The real two-loop action stays in every true subspace containing its actual input and retained secant vectors.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: Each genuine backward and forward update is a real observed vector combination. -/
theorem inverseBFGSApply_mem (c : ℝ) (W : List (E × E)) (K : Submodule ℝ E)
    (hW : ∀ p∈W, p.1∈K ∧ p.2∈K) {v : E} (hv : v∈K) : inverseBFGSApply c W v∈K := by
  -- Both genuine passes stay inside the actual observed subspace.
  induction W generalizing v with
  | nil => exact K.smul_mem c hv
  | cons p W ih =>
    simp only [inverseBFGSApply]
    exact K.add_mem
      (ih (fun q hq => hW q (List.mem_cons_of_mem p hq))
        (K.sub_mem hv (K.smul_mem _ (hW p List.mem_cons_self).2)))
      (K.smul_mem _ (hW p List.mem_cons_self).1)

/-- On genuine conjugate pairs and an actually step-orthogonal input, the real inverse-BFGS action has its exact diagonal coefficient formula.
Use: On genuine conjugate pairs and an actually step-orthogonal input, the real inverse-BFGS action has its exact diagonal coefficient formula.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: The true backward coefficients vanish; the actual older forward contributions are orthogonal to the next retained image. -/
theorem inverseBFGSApply_conjugate (c : ℝ) (W : List (E × E)) (v : E)
    (hg : ∀ p∈W, inner ℝ p.1 v=0)
    (hconj : W.Pairwise (fun p q => inner ℝ p.2 q.1=0)) :
    inverseBFGSApply c W v=c • v-
      (W.map fun p => (c*((inner ℝ p.1 p.2)⁻¹*inner ℝ p.2 v)) • p.1).sum := by
  -- The actual backward pass vanishes and true conjugacy fixes every subsequent forward coefficient.
  induction W with
  | nil => simp [inverseBFGSApply]
  | cons p W ih =>
    have htail := (List.pairwise_cons.mp hconj).2
    have hcross := (List.pairwise_cons.mp hconj).1
    rw [inverseBFGSApply,hg p List.mem_cons_self,mul_zero,zero_smul,sub_zero,
      ih (fun q hq => hg q (List.mem_cons_of_mem p hq)) htail]
    have hy : inner ℝ p.2
        (c • v-(W.map fun q => (c*((inner ℝ q.1 q.2)⁻¹*inner ℝ q.2 v)) • q.1).sum)=c*inner ℝ p.2 v := by
      have hz : inner ℝ p.2 ((W.map fun q => (c*((inner ℝ q.1 q.2)⁻¹*inner ℝ q.2 v)) • q.1).sum)=0 := by
        have hz' : ∀ L : List (E × E), (∀ q∈L, inner ℝ p.2 q.1=0) →
            inner ℝ p.2 ((L.map fun q => (c*((inner ℝ q.1 q.2)⁻¹*inner ℝ q.2 v)) • q.1).sum)=0 := by
          intro L hL
          induction L with
          | nil => simp
          | cons q L ih =>
            simp only [List.map_cons,List.sum_cons,inner_add_right,real_inner_smul_right,
              hL q List.mem_cons_self,mul_zero,zero_add]
            exact ih (fun z hz => hL z (List.mem_cons_of_mem q hz))
        exact hz' W hcross
      rw [inner_sub_right,real_inner_smul_right,hz,sub_zero]
    rw [hy,List.map_cons,List.sum_cons]
    simp only [sub_eq_add_neg,neg_add_rev]
    module


/-- The genuine inverse-BFGS direction is the scalar multiple of the actual FC block direction on true conjugate reference data.
Use: The genuine inverse-BFGS direction is the scalar multiple of the actual FC block direction on true conjugate reference data.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: Use the proved actual two-loop formula; genuine nonzero diagonal pivots give the true block inverse, and the physical coefficient sums coincide. -/
theorem inverseBFGSApply_eq_conjugacy (c : ℝ) (W : List (E × E)) (v : E)
    (hg : ∀ i, inner ℝ (windowSteps W i) v=0)
    (hdiag : ∀ i, inner ℝ (windowSteps W i) (windowImages W i)≠0)
    (hoff : ∀ i j, i≠j → inner ℝ (windowImages W i) (windowSteps W j)=0) :
    -inverseBFGSApply c W v=c • windowDirection W v := by
  -- Prove the actual diagonal block inverse on its genuine nonzero pivot domain.
  have hWg : ∀ p∈W, inner ℝ p.1 v=0 := by
    intro p hp
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    simpa only [windowSteps,hi] using hg i
  have hpair : W.Pairwise (fun p q => inner ℝ p.2 q.1=0) := by
    apply List.pairwise_iff_get.mpr
    intro i j hij
    exact hoff i j (ne_of_lt hij)
  rw [inverseBFGSApply_conjugate c W v hWg hpair]
  have hGram : crossGram (windowImages W) (windowSteps W)=
      Matrix.diagonal (fun i => inner ℝ (windowSteps W i) (windowImages W i)) := by
    ext i j
    by_cases he : i=j
    · subst j
      simp only [crossGram,Matrix.diagonal_apply_eq,real_inner_comm]
    · simp only [crossGram,Matrix.diagonal_apply_ne _ he,hoff i j he]
  have hsum : (W.map fun p => (c*((inner ℝ p.1 p.2)⁻¹*inner ℝ p.2 v)) • p.1).sum=
      ∑ i, (c*((inner ℝ (windowSteps W i) (windowImages W i))⁻¹*inner ℝ (windowImages W i) v)) • windowSteps W i := by
    conv_lhs => rw [← List.ofFn_get W,List.map_ofFn,List.sum_ofFn]
    rfl
  rw [hsum]
  have hInv : (Matrix.diagonal (fun i => inner ℝ (windowSteps W i) (windowImages W i)))⁻¹=
      Matrix.diagonal (fun i => (inner ℝ (windowSteps W i) (windowImages W i))⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [hdiag]
    · simp [Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij]
  simp only [windowDirection,conjugacyDirection,conjugacyCoefficients,hGram,hInv]
  simp only [combine,coordinates,Matrix.mulVec_diagonal,smul_add,smul_neg,Finset.smul_sum,smul_smul]
  module

/-- The actual data-only correction-free BFGS or L-BFGS method with its genuine retention and scalar initialization rule.
Use: The actual data-only correction-free BFGS or L-BFGS method with its genuine retention and scalar initialization rule.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: Full retention gives BFGS; a positive finite newest-retaining window gives L-BFGS. -/
def lbfgsMethod (memory : ℕ → ℕ) (scale : History E → ℝ) : ProbedMethod E where
  direction H := -inverseBFGSApply (scale H) (selectedWindow memory H) H.gradient
  correction _ _ := .done

/-- The actual BFGS/L-BFGS policy obeys the real source information class on every input history.
Use: The actual BFGS/L-BFGS policy obeys the real source information class on every input history.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: All true two-loop vectors are combinations of the actual current gradient and retained observed steps/secants; the real correction tree is empty. -/
theorem lbfgsMethod_spanRestricted (memory : ℕ → ℕ) (scale : History E → ℝ) :
    ProbedSpanRestricted memory (lbfgsMethod memory scale) := by
  -- This admissibility argument uses arbitrary real histories and no quadratic hypothesis.
  intro H
  refine ⟨H.observedSpan.neg_mem (inverseBFGSApply_mem _ _ _ ?_ H.gradient_mem_observedSpan),fun _ => trivial⟩
  intro p hp
  have hp' : p∈H.pairs := List.mem_of_mem_take hp
  constructor
  · exact Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨p,hp',rfl⟩)))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨p,hp',rfl⟩))

/-- Every actual two-loop inverse-BFGS action sends zero input to zero, including singular supplied pairs.
Use: Every actual two-loop inverse-BFGS action sends zero input to zero, including singular supplied pairs.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: The genuine two passes have only zero scalar numerators and vectors. -/
theorem inverseBFGSApply_zero (c : ℝ) (W : List (E × E)) : inverseBFGSApply c W (0 : E)=0 := by
  induction W with
  | nil => exact smul_zero c
  | cons p W ih => simp [inverseBFGSApply,ih]

/-- Distinct genuine reference CG steps have exactly zero true curvature pairing.
Use: Distinct genuine reference CG steps have exactly zero true curvature pairing.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: Scale the already proved actual CG direction conjugacy, choosing the true index order and using actual symmetry. -/
theorem referenceStep_conjugate (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i < k, CG.gradient Q g i≠0) (i j : ℕ) (hi : i < k) (hj : j < k) (hij : i≠j) :
    inner ℝ (Q (referenceStep Q g i)) (referenceStep Q g j)=0 := by
  -- Transfer the genuine ordered CG conjugacy invariant to the actual scaled physical steps.
  have hinv := CG.invariant Q hQ hpos g k hpre
  have hc : inner ℝ (Q (CG.direction Q g i)) (CG.direction Q g j)=0 := by
    rcases lt_or_gt_of_ne hij with h|h
    · have hs := hQ (CG.direction Q g i) (CG.direction Q g j)
      change inner ℝ (Q (CG.direction Q g i)) (CG.direction Q g j)=inner ℝ (CG.direction Q g i) (Q (CG.direction Q g j)) at hs
      rw [hs,hinv.conjugate i j h hj.le]
    · rw [real_inner_comm,hinv.conjugate j i h hi.le]
  simp only [referenceStep,map_smul,real_inner_smul_left,real_inner_smul_right,hc,mul_zero]

/-- The actual retained inverse-BFGS direction is its genuine scalar initialization times the true CG direction, including the solved tail.
Use: The actual retained inverse-BFGS direction is its genuine scalar initialization times the true CG direction, including the solved tail.
Article: main_krylov, cor:lm and s3:cor:qn, genuine inverse-BFGS and limited-memory directions.
Proof: Actual retained steps have proved independent positive diagonal pivots, genuine CG orthogonality and true conjugacy. Apply the actual two-loop/block-solve identity and the already proved retained reference solve. -/
theorem inverseBFGSApply_reference (c : ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k M : ℕ)
    (hm : CG.gradient Q g k≠0 → 0 < k → 0 < M) :
    -inverseBFGSApply c ((referencePairs Q g k).take M) (CG.gradient Q g k)=c • CG.direction Q g k := by
  -- The actual zero-input branch needs no inverse or nonstagnation domain.
  by_cases hg : CG.gradient Q g k=0
  · rw [hg,inverseBFGSApply_zero,neg_zero,direction_zero_of_gradient Q g k hg,smul_zero]
  have hpre : ∀ i < k, CG.gradient Q g i≠0 := by
    intro i hi hz
    exact hg (CG.gradient_eq_zero_of_le Q g hz hi.le)
  let W := (referencePairs Q g k).take M
  have hval (i : Fin W.length) : i.val < k := by
    have := i.isLt
    simp only [W,List.length_take,referencePairs_length] at this
    omega
  have hi (i : Fin W.length) : k-1-i.val < k := by have := hval i;omega
  have hs (i : Fin W.length) : windowSteps W i=referenceStep Q g (k-1-i.val) :=
    congrArg Prod.fst (retained_pair Q g k M i)
  have hy (i : Fin W.length) : windowImages W i=Q (referenceStep Q g (k-1-i.val)) :=
    congrArg Prod.snd (retained_pair Q g k M i)
  rw [inverseBFGSApply_eq_conjugacy,windowDirection_reference Q hQ hpos g k M hg (hm hg)]
  · intro i
    rw [hs,referenceStep,real_inner_smul_left,(CG.invariant Q hQ hpos g k hpre).old_direction _ (hi i),mul_zero]
  · intro i
    rw [hy,← hs]
    exact (hpos _ ((retainedSteps_independent Q hQ hpos g k M hpre).ne_zero i)).ne'
  · intro i j hij
    rw [hy,hs]
    apply referenceStep_conjugate Q hQ hpos g k hpre _ _ (hi i) (hi j)
    intro he
    apply hij
    apply Fin.ext
    have := hval i
    have := hval j
    change k-1-i.val=k-1-j.val at he
    omega

end
end krylov.Methods
