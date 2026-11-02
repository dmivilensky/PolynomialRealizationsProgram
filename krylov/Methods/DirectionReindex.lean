import krylov.Methods.XRFCShortPrefix

/-!
Article: main_krylov, lem:U, fixed-coordinate form of actual observed-window solves.
Use: identify the actual newest-first list solve with its fixed finite
coordinate family, so adaptive trajectory regularity concerns the real algorithm.
Source: invariance of finite sums and actual matrix inverse under bijective reindexing.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Bijectively relabeling actual observed vectors relabels the actual computed conjugacy coefficients.
Use: fixed finite coordinates describe the same implemented solve as its actual list indices.
Article: main_krylov, lem:U, finite observed coefficient coordinates.
Source: mathlib Matrix.inv_submatrix_equiv and Equiv.sum_comp.
Proof: the actual cross Gram matrix and its inverse reindex together; the
finite right-hand-side sum is unchanged after a bijective change of index. -/
theorem conjugacyCoefficients_reindex (e : κ ≃ ι) (s y : ι → E) (g : E) (i : κ) :
    conjugacyCoefficients (s ∘ e) (y ∘ e) g i=conjugacyCoefficients s y g (e i) := by
  -- No nonsingularity hypothesis is needed: the implemented totalized inverse itself respects relabeling.
  have hC : crossGram (y ∘ e) (s ∘ e)=(crossGram y s).submatrix e e := rfl
  unfold conjugacyCoefficients
  rw [hC,Matrix.inv_submatrix_equiv]
  change (∑ j, (crossGram y s)⁻¹ (e i) (e j)*inner ℝ (y (e j)) g)=
    ∑ j, (crossGram y s)⁻¹ (e i) j*inner ℝ (y j) g
  exact Equiv.sum_comp e (fun j : ι => (crossGram y s)⁻¹ (e i) j*inner ℝ (y j) g)

/-- The actual computed physical conjugacy direction is invariant under every bijective relabeling of its observed window.
Use: changing from real list indices to fixed finite coordinates preserves the exact algorithm, including singular totalized cases.
Article: main_krylov, lem:U, coordinate-independent computed direction.
Proof: the proved coefficients reindex with the vectors, and their actual finite physical sum is unchanged. -/
theorem conjugacyDirection_reindex (e : κ ≃ ι) (s y : ι → E) (g : E) :
    conjugacyDirection (s ∘ e) (y ∘ e) g=conjugacyDirection s y g := by
  unfold conjugacyDirection combine
  simp only [conjugacyCoefficients_reindex,Function.comp_apply]
  rw [Equiv.sum_comp e (fun i => conjugacyCoefficients s y g i • s i)]

/-- The actual complete newest-first transcript direction solve equals its fixed chronological-age coordinate solve.
Use: derive analytic regularity of the actual adaptive FC direction from its genuine finite data coordinates.
Article: main_krylov, lem:U, actual full-window solve.
Proof: each actual list entry has its proved chronological age and the real
list length equals the fixed iteration count; the computed physical solve is invariant under this bijective index cast. -/
theorem windowDirection_executed (s y : ℕ → E) (g : E) (k : ℕ) :
    windowDirection (executedPairs s y k) g=
      conjugacyDirection (fun i : Fin k => s (k-1-i.val)) (fun i : Fin k => y (k-1-i.val)) g := by
  -- The equality is exact for every data family, not merely near a quadratic reference.
  let W := executedPairs s y k
  let e : Fin W.length ≃ Fin k := finCongr (executedPairs_length s y k)
  have hs : windowSteps W=(fun i : Fin k => s (k-1-i.val)) ∘ e := by
    funext i
    change (W[i.val]).1=_
    rw [executedPairs_get s y k i.val (by simpa only [W,executedPairs_length] using i.isLt)]
    rfl
  have hy : windowImages W=(fun i : Fin k => y (k-1-i.val)) ∘ e := by
    funext i
    change (W[i.val]).2=_
    rw [executedPairs_get s y k i.val (by simpa only [W,executedPairs_length] using i.isLt)]
    rfl
  change conjugacyDirection (windowSteps W) (windowImages W) g=_
  rw [hs,hy,conjugacyDirection_reindex]

/-- The actual full-memory FC direction has its exact fixed finite-age coordinate formula.
Use: local regularity proofs differentiate the real executed data-only FC policy.
Article: main_krylov, lem:U, actual adaptive FC coefficient solve.
Proof: the proved complete actual pair transcript identifies the real window;
the exact reindexing theorem gives its fixed finite coefficient formula. -/
theorem fullFC_direction_array (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    fcDirection fullMemory A g k=
      conjugacyDirection (fun i : Fin k => fcStep fullMemory A g (k-1-i.val))
        (fun i : Fin k => fcSecant fullMemory A g (k-1-i.val)) (fcGradient fullMemory A g k) := by
  change windowDirection (selectedWindow fullMemory (fcHistory fullMemory A g k)) _=_
  rw [fullFC_window,windowDirection_executed]
  rfl

/-- The determinant of the actual complete observed conjugacy matrix equals the determinant in fixed chronological-age coordinates.
Use: prove openness of the actual full-memory coefficient-solve domain from analytic finite coordinates.
Article: main_krylov, lem:U, secant determinant domains.
Proof: actual list ages are a bijective finite coordinate cast, and determinant is unchanged by simultaneous row and column reindexing. -/
theorem crossGram_executed_det (s y : ℕ → E) (k : ℕ) :
    (crossGram (windowImages (executedPairs s y k)) (windowSteps (executedPairs s y k))).det=
      (crossGram (fun i : Fin k => y (k-1-i.val)) (fun i : Fin k => s (k-1-i.val))).det := by
  -- The same cast is used on both matrix axes, so no determinant sign is introduced.
  let W := executedPairs s y k
  let e : Fin W.length ≃ Fin k := finCongr (executedPairs_length s y k)
  have he : crossGram (windowImages W) (windowSteps W)=
      (crossGram (fun i : Fin k => y (k-1-i.val)) (fun i : Fin k => s (k-1-i.val))).submatrix e e := by
    ext i j
    have hi := executedPairs_get s y k i.val (by simpa only [W,executedPairs_length] using i.isLt)
    have hj := executedPairs_get s y k j.val (by simpa only [W,executedPairs_length] using j.isLt)
    change inner ℝ (W[i.val]).2 (W[j.val]).1=_
    rw [hi,hj]
    rfl
  rw [he,Matrix.det_submatrix_equiv_self]

/-- The actual executed full-memory conjugacy determinant has its fixed finite analytic coordinate formula.
Use: establish the genuine open domain of the real adaptive FC implementation.
Article: main_krylov, lem:U, actual FC solve domains.
Proof: substitute the real full observed pair transcript and its proved determinant reindexing identity. -/
theorem fullFC_conjugacy_det_array (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (crossGram (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det=
      (crossGram (fun i : Fin k => fcSecant fullMemory A g (k-1-i.val))
        (fun i : Fin k => fcStep fullMemory A g (k-1-i.val))).det := by
  rw [fullFC_window,crossGram_executed_det]

end
end krylov.Methods
