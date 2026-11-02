import krylov.Methods.ProbedModelBasis

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist and lem:U, genuine parametric full observed-model regularity.
Use: derive real joint C-two regularity of the actual full model basis and image family from primitive source-class membership on arbitrary normed parameter spaces.
Source: proved genuine primitive-derived actual direction/probe/step fields and true gradient-prefix regularity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual full current-direction and old-step family is jointly C-two in every genuine smooth operator parameter.
Use: The actual full current-direction and old-step family is jointly C-two in every genuine smooth operator parameter.
Article: main_krylov, apB:prop:consist and lem:U, genuine parametric full observed-model regularity.
Proof: Extract the real current direction and true chronological old steps from actual primitive-derived field regularity. -/
theorem smoothProbed_stepBasis_parametric (M : SmoothProbedClass E)
    (A B : X → ℕ → E →L[ℝ] E) (g : E) (x : X) (k : ℕ)
    (hA : ∀ i<k+1,ContDiffAt ℝ 2 (fun p => A p i) x)
    (hB : ∀ i<k+1,ContDiffAt ℝ 2 (fun p => B p i) x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) :
    ContDiffAt ℝ 2 (fun p => probedStepBasis M.policy (A p) (B p) g k) x := by
  -- Genuine primitive coefficient membership derives the actual observed fields on the full parameter space.
  have hs := M.smooth Q hQ hpos g (k+1) hpre
  have hf i hi := smoothProbed_fields_regular M.policy M.consistent A B (fun _ => g) x (k+1)
    hA hB contDiffAt_const Q hAx hBx hQ hpos hpre hs i hi
  apply contDiffAt_pi.mpr
  refine Fin.cases (hf k (by omega)).1 (fun i => ?_)
  exact (hf (k-1-i.val) (by have := i.isLt;omega)).2.2.1

/-- The actual full probe and old-secant image family is jointly C-two in every genuine smooth operator parameter.
Use: The actual full probe and old-secant image family is jointly C-two in every genuine smooth operator parameter.
Article: main_krylov, apB:prop:consist and lem:U, genuine parametric full observed-model regularity.
Proof: Use genuine current-probe regularity and actual differences of true earlier gradient-prefix outputs. -/
theorem smoothProbed_imageBasis_parametric (M : SmoothProbedClass E)
    (A B : X → ℕ → E →L[ℝ] E) (g : E) (x : X) (k : ℕ)
    (hA : ∀ i<k+1,ContDiffAt ℝ 2 (fun p => A p i) x)
    (hB : ∀ i<k+1,ContDiffAt ℝ 2 (fun p => B p i) x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) :
    ContDiffAt ℝ 2 (fun p => probedImageBasis M.policy (A p) (B p) g k) x := by
  have hs := M.smooth Q hQ hpos g (k+1) hpre
  -- Each genuine stored image is the actual difference of two smooth earlier gradient prefixes.
  have hG (j : ℕ) (hj : j≤k+1) : ContDiffAt ℝ 2 (fun p => probedGradient M.policy (A p) (B p) g j) x :=
    smoothProbed_gradient_regular M.policy M.consistent A B (fun _ => g) x j
      (fun i hi => hA i (hi.trans_le hj)) (fun i hi => hB i (hi.trans_le hj)) contDiffAt_const
      Q hAx hBx hQ hpos (fun i hi => hpre i (hi.trans_le hj)) (hs.mono M.policy hj)
  apply contDiffAt_pi.mpr
  refine Fin.cases ?_ (fun i => ?_)
  · exact (smoothProbed_fields_regular M.policy M.consistent A B (fun _ => g) x (k+1)
      hA hB contDiffAt_const Q hAx hBx hQ hpos hpre hs k (by omega)).2.1
  · exact (hG (k-1-i.val+1) (by omega)).sub (hG (k-1-i.val) (by omega))
end
end krylov.Methods
