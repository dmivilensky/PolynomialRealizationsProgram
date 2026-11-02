import krylov.Cancellation.DCSlide
import krylov.Methods.CorrectionFreeSearch
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(a,c).
Use: locate every genuinely retained chronological pair and unroll the exact
residual recursion on the actual DC-slide run, including sliding windows.
Source: actual newest-first history indexing and finite variation of constants;
the finite recursion and its product weights are proved here.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A pair whose actual age is inside the prescribed memory is truly retained.
Use: the residual identities apply to source suffix windows, with no assumed
pair-membership witness supplied by the algorithm.
Article: main_krylov, thm:dcs(a).
Proof: locate its newest-first chronological age in the actual taken transcript. -/
theorem probed_pair_retained (m : ProbedMethod E) (memory : ℕ → ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k)
    (hkeep : k-1-i<memory k) :
    (probedStep m A B g i,probedSecant m A B g i)∈selectedWindow memory (methodRun m A B g k) := by
  rw [selectedWindow_methodRun]
  apply List.mem_iff_getElem.mpr
  refine ⟨k-1-i,by simp only [List.length_take,executedPairs_length]; omega,?_⟩
  rw [List.getElem_take,executedPairs_get _ _ k (k-1-i) (by omega)]
  have he : k-1-(k-1-i)=i := by omega
  rw [he]

/-- A chronological one-gradient pair is truly in its prescribed retained suffix.
Use: exact fresh-defect cancellation refers to actual recorded operator images.
Article: main_krylov, thm:dcs(c).
Proof: use the actual one-gradient secant transcript and its genuine record count. -/
theorem one_gradient_pair_retained (m : OneGradientMethod E) (memory : ℕ → ℕ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k)
    (hkeep : k-1-i<memory k) :
    (oneGradientStep m A g i,A i (oneGradientStep m A g i))∈
      selectedWindow memory (oneGradientRun m A g k) := by
  change _∈(oneGradientRun m A g k).pairs.take (memory (oneGradientRun m A g k).records.length)
  rw [oneGradientRun_length,oneGradientRun_pairs_segmentOperators]
  apply List.mem_iff_getElem.mpr
  refine ⟨k-1-i,by simp only [List.length_take,executedPairs_length]; omega,?_⟩
  rw [List.getElem_take,executedPairs_get _ _ k (k-1-i) (by omega)]
  have he : k-1-(k-1-i)=i := by omega
  rw [he]

/-- The exact finite product formula for a residual starting at zero.
Use: apply variation of constants after the actual search first annihilates a
step's own residual.
Article: main_krylov, thm:dcs(c).
Proof: append one true forcing term and extend every older chronological product
by the actual newest multiplier. -/
theorem residual_recursion_unroll (r e d : ℕ → ℝ) (hzero : r 0=0)
    (N : ℕ) (hrec : ∀ k<N,r (k+1)=e k*r k+d k) :
    r N=∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,e l)*d j := by
  induction N with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty] using hzero
  | succ N ih =>
    rw [hrec N (Nat.lt_succ_self N),ih (fun k hk => hrec k (by omega)),Finset.sum_range_succ]
    have hlast : (∏ l∈Finset.Ico (N+1) (N+1),e l)=1 := by simp
    rw [hlast,one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.prod_Ico_succ_top (by have := Finset.mem_range.mp hj; omega)]
    ring

/-- Earlier members of a nondecreasing-oldest-index suffix remain active until
the given final iteration whenever they are active there.
Use: justify all intermediate residual recursions for the source sliding windows.
Article: main_krylov, s8:dcsdef and thm:dcs(c).
Proof: monotonicity of the true oldest retained index gives the earlier age bound. -/
theorem retained_between (memory : ℕ → ℕ) (hm : Monotone (fun k => k-memory k))
    {i j k : ℕ} (hij : i<j) (hjk : j≤k) (hkeep : k-1-i<memory k) :
    j-1-i<memory j := by
  have hmono := hm hjk
  change j-memory j≤k-memory k at hmono
  omega

/-- The actual exact-search DC-slide recursion holds for every source-retained pair.
Use: expose the chronological finite-variation identity directly to later estimates.
Article: main_krylov, thm:dcs(a).
Proof: derive actual retained-pair membership from the memory rule before
applying the proved genuine observed tilted solve. -/
theorem dc_slide_retained_residual (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k) (hkeep : k-1-i<memory k)
    (hAi : (A i).toLinearMap.IsSymmetric)
    (hdet : IsUnit (crossGram
      (windowImages (selectedWindow memory (methodRun (dcSlideMethod memory estimate) A B g k)))
      (windowSteps (selectedWindow memory (methodRun (dcSlideMethod memory estimate) A B g k)))).det) :
    let m := dcSlideMethod memory estimate
    let H := methodRun m A B g k
    let t := lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k)
    inner ℝ (probedStep m A B g i) (probedGradient m A B g (k+1))=
      (1-t/estimate H)*inner ℝ (probedStep m A B g i) (probedGradient m A B g k)+
        inner ℝ (probedStep m A B g i) ((A k-A i) (probedStep m A B g k)) :=
  dc_slide_residual memory estimate A B g k i hAi
    (probed_pair_retained _ memory A B g k i hi hkeep) hdet

/-- One-gradient DC-slide leaves precisely the fresh defect on every actually
retained old step, for arbitrary finite operator variation.
Use: no small-variation or asymptotic hypothesis is needed for this source identity.
Article: main_krylov, thm:dcs(c).
Proof: derive actual chronological window membership and use the same nonzero
data estimate in the real evaluated step and the real tilted solve. -/
theorem dc_slide_retained_fresh (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k) (hkeep : k-1-i<memory k)
    (hAi : (A i).toLinearMap.IsSymmetric)
    (hdet : IsUnit (crossGram
      (windowImages (selectedWindow memory (oneGradientRun (dcSlideOneGradient memory estimate) A g k)))
      (windowSteps (selectedWindow memory (oneGradientRun (dcSlideOneGradient memory estimate) A g k)))).det)
    (ha : estimate (oneGradientRun (dcSlideOneGradient memory estimate) A g k)≠0) :
    let m := dcSlideOneGradient memory estimate
    inner ℝ (oneGradientStep m A g i) (oneGradientGradient m A g (k+1))=
      inner ℝ (oneGradientStep m A g i) ((A k-A i) (oneGradientStep m A g k)) :=
  dc_slide_one_gradient_fresh memory estimate A g k i hAi
    (one_gradient_pair_retained _ memory A g k i hi hkeep) hdet ha

/-- The actual exact-search residual after any retained interval is the exact
sum of its physical fresh defects with chronological damping products.
Use: this stronger finite identity is the starting point for the source's
linearized product formula and stale-defect bounds.
Article: main_krylov, thm:dcs(c).
Proof: the real search first makes the step's own residual zero. Each later
actual retained solve satisfies the proved residual identity; bounded finite
variation of constants then gives the printed product weights. -/
theorem dc_slide_residual_products (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (i N : ℕ)
    (hAi : (A i).toLinearMap.IsSymmetric)
    (hkeep : ∀ j<N,(i+1+j)-1-i<memory (i+1+j))
    (hdet : ∀ j<N,IsUnit (crossGram
      (windowImages (selectedWindow memory (methodRun (dcSlideMethod memory estimate) A B g (i+1+j))))
      (windowSteps (selectedWindow memory (methodRun (dcSlideMethod memory estimate) A B g (i+1+j))))).det) :
    let m := dcSlideMethod memory estimate
    let epsilon := fun k => 1-
      lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k)/
        estimate (methodRun m A B g k)
    inner ℝ (probedStep m A B g i) (probedGradient m A B g (i+1+N))=
      ∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,epsilon (i+1+l))*
        inner ℝ (probedStep m A B g i) ((A (i+1+j)-A i) (probedStep m A B g (i+1+j))) := by
  let m := dcSlideMethod memory estimate
  let r := fun j => inner ℝ (probedStep m A B g i) (probedGradient m A B g (i+1+j))
  let e := fun j => 1-
    lineLength (probedGradient m A B g (i+1+j)) (probedDirection m A B g (i+1+j))
      (probedProbe m A B g (i+1+j))/estimate (methodRun m A B g (i+1+j))
  let d := fun j => inner ℝ (probedStep m A B g i)
    ((A (i+1+j)-A i) (probedStep m A B g (i+1+j)))
  have hz : r 0=0 := by
    exact correctionFree_last_residual m (dc_slide_correction_free memory estimate) A B g i
  have hr (j : ℕ) (hj : j<N) : r (j+1)=e j*r j+d j := by
    have he := dc_slide_retained_residual memory estimate A B g (i+1+j) i
      (by omega) (hkeep j hj) hAi (hdet j hj)
    convert he using 1
  exact residual_recursion_unroll r e d hz N hr

end
end krylov.Cancellation
