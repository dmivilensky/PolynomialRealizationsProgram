import krylov.Methods.BroydenReferenceModel

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine convex Broyden primitive pivot domains.
Use: derive every actual secant and old-model inverse-curvature denominator required by true finite observed Broyden coefficients on active quadratic references.
Source: proved genuine accumulated-model CG invariants, true consecutive reference pair algebra and real positivity of actual residual and direction scales.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual finite inverse convex Broyden recursion has genuine nonzero secant and inverse-curvature pivots at every real chronological update.
Use: The actual finite inverse convex Broyden recursion has genuine nonzero secant and inverse-curvature pivots at every real chronological update.
Article: main_krylov, def:classes, genuine convex Broyden primitive pivot domains.
Proof: Require the two true denominators and recursively retain the genuine older observed-pair domain. -/
def BroydenPivots (c : ℝ) (θ : ℕ → ℝ) : List (E × E) → Prop
  | [] => True
  | (s,y)::W => inner ℝ s y≠0 ∧ inner ℝ y (inverseBroydenModel c θ W y)≠0 ∧ BroydenPivots c θ W

/-- Each actual active reference secant pair has genuinely positive secant curvature and positive true older-model inverse curvature.
Use: Each actual active reference secant pair has genuinely positive secant curvature and positive true older-model inverse curvature.
Article: main_krylov, def:classes, genuine convex Broyden primitive pivot domains.
Proof: Use the genuine positive current model scale and actual future-gradient action to identify both real pair denominators exactly. -/
theorem broyden_reference_pair_pivots_pos (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) :
    0 < inner ℝ (referenceStep Q g k) (Q (referenceStep Q g k)) ∧
    0 < inner ℝ (Q (referenceStep Q g k))
      (inverseBroydenModel c θ (referencePairs Q g k) (Q (referenceStep Q g k))) := by
  -- The actual accumulated model gives a genuine positive current scale and its true next-gradient action.
  obtain ⟨a,ha,hg,hfuture⟩ := inverseBroydenModel_reference_prefix c hc θ hθ Q hQ hpos g (k+1) hpre k (by omega)
  have hIk := CG.invariant Q hQ hpos g k (fun i hi => hpre i (by omega))
  have hIn := CG.invariant Q hQ hpos g (k+1) hpre
  have hgd : inner ℝ (CG.gradient Q g k) (CG.direction Q g k)= -‖CG.gradient Q g k‖^2 := by
    rw [real_inner_comm];exact hIk.search_pair
  have hrd : inner ℝ (CG.gradient Q g (k+1)) (CG.direction Q g k)=0 := by
    rw [real_inner_comm];exact hIn.old_direction k (by omega)
  have hgr := hIn.old_gradient k (by omega)
  have hr := hfuture (k+1) (by omega) le_rfl
  have hp := broyden_reference_pair_data (inverseBroydenModel c θ (referencePairs Q g k))
    (CG.gradient Q g k) (CG.gradient Q g (k+1)) (CG.direction Q g k) c a (CG.length Q g k) hg hr hgd hrd hgr
  have hy : Q (referenceStep Q g k)=CG.gradient Q g (k+1)-CG.gradient Q g k := by
    rw [referenceStep,map_smul]
    exact (CG.gradient_change Q g k).symm
  -- Genuine nonzero reference residuals make both actual denominators strictly positive.
  have hA : 0<‖CG.gradient Q g k‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (hpre k (by omega)))
  constructor
  · rw [hy]
    exact hp.2.1.symm ▸ mul_pos (CG.invariant_line_pos Q hpos g k hIk (hpre k (by omega))).2.1 hA
  · rw [hy,hp.1]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le (sq_nonneg _)) (mul_pos ha hA)

/-- Every genuine active reference-pair prefix satisfies all actual inverse convex Broyden primitive pivot domains.
Use: Every genuine active reference-pair prefix satisfies all actual inverse convex Broyden primitive pivot domains.
Article: main_krylov, def:classes, genuine convex Broyden primitive pivot domains.
Proof: Induct through the true chronological reference pairs using both proved genuine positive current pivots. -/
theorem broyden_reference_pivots (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k,CG.gradient Q g i≠0) :
    BroydenPivots c θ (referencePairs Q g k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    have hp := broyden_reference_pair_pivots_pos c hc θ hθ Q hQ hpos g k hpre
    exact ⟨hp.1.ne',hp.2.ne',ih (fun i hi => hpre i (by omega))⟩
end
end krylov.Methods
