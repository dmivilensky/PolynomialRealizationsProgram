import krylov.Methods.SecantSolve
import krylov.Reference.Stopping

/-!
Article: main_krylov, lem:consistent(a,c), quadratic consistency of retained windows.
Use: prove the data-only conjugacy solve equals the actual CG direction for
every subset of earlier steps retaining the newest one. All independence and
nonzero denominators are derived from the executed CG recurrence.
Source: the classical retained-newest-pair CG identity; the window extension
of block conjugacy discussed at KoldaEtAl98 in the source article.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference Matrix
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The actual generic physical CG step.
Use: reference window statements apply in arbitrary real inner-product spaces.
Article: main_krylov, s2:eq:cg and lem:consistent, s_k⁰=α_kd_k⁰. -/
def referenceStep (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  CG.length Q g k • CG.direction Q g k

/-- The totalized true CG direction is zero whenever its current true gradient is zero.
Use: a concrete secant solver agrees with the stopped CG policy after exhaustion as well.
Article: main_krylov, lem:consistent, the solved tail.
Proof: at the initial state d₀=−g₀; at every later state the zero numerator of β annihilates the old direction. -/
theorem direction_zero_of_gradient (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hk : CG.gradient Q g k=0) : CG.direction Q g k=0 := by
  cases k with
  | zero => change g=0 at hk; change -g=0; rw [hk, neg_zero]
  | succ k =>
    rw [CG.direction_succ]
    simp only [CG.beta, hk, norm_zero, zero_pow (by omega : 2≠0), zero_div, zero_smul, neg_zero, add_zero]

/-- Nonzero mutually conjugate physical vectors are linearly independent.
Use: prove nonsingularity of every retained actual quadratic secant model.
Article: main_krylov, lem:consistent, independence of retained reference pairs.
Proof: pair a vanishing finite combination with each true operator image;
conjugacy isolates one coefficient, and positivity makes its diagonal pairing nonzero. -/
theorem conjugate_independent (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (s : ι → E)
    (hs : ∀ i, s i≠0) (ho : ∀ i j, i≠j → inner ℝ (s i) (Q (s j))=0) :
    LinearIndependent ℝ s := by
  -- A conjugate direction is detected by its own strictly positive curvature, independently of step scaling.
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he := congrArg (fun v => inner ℝ v (Q (s i))) hc
  simp only [sum_inner, real_inner_smul_left, inner_zero_left] at he
  rw [Finset.sum_eq_single i] at he
  · exact (mul_eq_zero.mp he).resolve_right (hpos _ (hs i)).ne'
  · intro j _ hji
    rw [ho j i hji, mul_zero]
  · simp

/-- Any injectively selected old actual CG steps form a genuinely independent retained window.
Use: the inverse in every quadratic FC/RFC model is justified from the actual finite prefix.
Article: main_krylov, lem:consistent(a), all retained CG windows.
Proof: actual positive lines make all retained steps nonzero; the computed
CG conjugacy invariant supplies the cross pairings, and positive conjugate independence applies. -/
theorem reference_window_independent (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) (idx : ι → ℕ)
    (hi : Function.Injective idx) (hr : ∀ i, idx i<k) :
    LinearIndependent ℝ (fun i => referenceStep Q g (idx i)) := by
  -- No lower bound on any retained step length is imposed in this exact consistency argument.
  have hk := CG.invariant Q hQ hpos g k hg
  apply conjugate_independent Q hpos
  · intro i
    obtain ⟨hd, hl, _⟩ := CG.invariant_line_pos Q hpos g (idx i)
      (CG.invariant Q hQ hpos g (idx i) (fun j hj => hg j (hj.trans (hr i)))) (hg (idx i) (hr i))
    exact smul_ne_zero hl.ne' hd
  · intro i j hij
    have hn : idx i≠idx j := fun h => hij (hi h)
    have hz : inner ℝ (CG.direction Q g (idx i)) (Q (CG.direction Q g (idx j)))=0 := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact hk.conjugate _ _ h (hr j).le
      · have he := hQ (CG.direction Q g (idx i)) (CG.direction Q g (idx j))
        change inner ℝ (Q (CG.direction Q g (idx i))) (CG.direction Q g (idx j))=
          inner ℝ (CG.direction Q g (idx i)) (Q (CG.direction Q g (idx j))) at he
        rw [← he, real_inner_comm]
        exact hk.conjugate _ _ h (hr i).le
    simp only [referenceStep, map_smul, real_inner_smul_left, real_inner_smul_right, hz, mul_zero]

variable [DecidableEq ι]

/-- The computed FC block solve recovers the actual CG direction from any retained window containing the newest pair.
Use: a single theorem covers full memory and every nonempty sliding suffix.
Article: main_krylov, lem:consistent(a), exact retained-window direction.
Proof: true CG is conjugate to every selected image and its correction to
−g_k is a multiple of the newest stored step; the actual nonsingular block-solve uniqueness identifies it. -/
theorem conjugacyDirection_reference (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) (idx : ι → ℕ)
    (hi : Function.Injective idx) (hr : ∀ i, idx i<k)
    (hnew : 0<k → ∃ i, idx i+1=k) :
    conjugacyDirection (fun i => referenceStep Q g (idx i))
      (fun i => Q (referenceStep Q g (idx i))) (CG.gradient Q g k)=CG.direction Q g k := by
  -- The candidate direction is characterized by its actual retained conjugacy and a data-visible newest-step displacement.
  have hli := reference_window_independent Q hQ hpos g k hg idx hi hr
  have hC := isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos hli).det_pos.ne'
  apply conjugacyDirection_unique _ _ _ _ hC
  · cases k with
    | zero =>
      change -g+g∈_
      rw [neg_add_cancel]
      exact Submodule.zero_mem _
    | succ k =>
      obtain ⟨i, hi⟩ := hnew (Nat.succ_pos k)
      have hidx : idx i=k := by omega
      have hl := (CG.invariant_line_pos Q hpos g k
        (CG.invariant Q hQ hpos g k (fun j hj => hg j (by omega))) (hg k (by omega))).2.1.ne'
      have he : CG.direction Q g (k+1)+CG.gradient Q g (k+1)=
          (CG.beta Q g k/CG.length Q g k) • referenceStep Q g (idx i) := by
        rw [CG.direction_succ, referenceStep, hidx, smul_smul, div_mul_cancel₀ _ hl]
        abel
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · ext i
    have hk := CG.invariant Q hQ hpos g k hg
    have he := hQ (CG.direction Q g (idx i)) (CG.direction Q g k)
    change inner ℝ (Q (CG.direction Q g (idx i))) (CG.direction Q g k)=
      inner ℝ (CG.direction Q g (idx i)) (Q (CG.direction Q g k)) at he
    simp only [coordinates, referenceStep, map_smul, real_inner_smul_left, Pi.zero_apply]
    rw [he, hk.conjugate _ _ (hr i) le_rfl, mul_zero]

/-- The data-only FC direction is zero for an actually zero current gradient, even with singular stored data.
Use: the totalized implementation agrees with the proved stopped reference without extra inverse assumptions.
Article: main_krylov, lem:consistent, finite stopping.
Proof: every actual coefficient right-hand side is zero. -/
theorem conjugacyDirection_zero (s y : ι → E) : conjugacyDirection s y (0 : E)=0 := by
  have hz : coordinates y (0 : E)=0 := by ext i; exact inner_zero_right _
  simp only [conjugacyDirection, conjugacyCoefficients, hz, Matrix.mulVec_zero, combine,
    Pi.zero_apply, zero_smul, Finset.sum_const_zero, neg_zero, add_zero]

/-- Every actual old CG step is orthogonal to the actual post-search gradient.
Use: the whole augmented RFC projected residual is zero before any correction is computed.
Article: main_krylov, lem:consistent(a), zero quadratic corrections.
Proof: use the computed next-state invariant, which requires nonzero gradients only before that next state. -/
theorem referenceStep_postsearch_orth (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) {i : ℕ} (hi : i≤k) :
    inner ℝ (referenceStep Q g i) (CG.gradient Q g (k+1))=0 := by
  have hk := CG.invariant Q hQ hpos g (k+1) (fun j hj => hg j (by omega))
  rw [referenceStep, real_inner_smul_left, hk.old_direction i (by omega), mul_zero]

end
end krylov.Methods
