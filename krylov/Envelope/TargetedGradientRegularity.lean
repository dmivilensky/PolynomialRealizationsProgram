import krylov.Methods.TargetedOutput
import krylov.Methods.FullModelRegularity
import krylov.Methods.ProbedModelReference
import krylov.Methods.FCSmoothClass
import krylov.Envelope.TargetModelJet

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine target-method output regularity.
Use: derive actual joint C-two regularity of the real reference-targeted final gradient directly from its primitive observed FC prefix and true nonsingular model.
Source: genuine parametric full-model basis/image regularity, actual positive quadratic model domains and the proved real target-relative model output.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability Matrix
open scoped Matrix.Norms.Elementwise
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual target-relative terminal gradient is jointly C-two in genuine smooth operator parameters on every true active reference cycle.
Use: The actual target-relative terminal gradient is jointly C-two in genuine smooth operator parameters on every true active reference cycle.
Article: main_krylov, apB:prop:consist, genuine target-method output regularity.
Proof: Derive the true FC prefix fields and real positive model domain; identify the actually executed target query and apply genuine inverse-model output calculus. -/
theorem targeted_gradient_regular (target : E)
    (A B : X → ℕ → E →L[ℝ] E) (g : E) (x : X) (k : ℕ)
    (hA : ∀ i<k+1,ContDiffAt ℝ 2 (fun p => A p i) x)
    (hB : ∀ i<k+1,ContDiffAt ℝ 2 (fun p => B p i) x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) :
    ContDiffAt ℝ 2 (fun p => probedGradient (targetedFinalMethod (k+1) target) (A p) (B p) g (k+1)) x := by
  -- The genuine FC prefix supplies all actual primitive-derived joint model and incoming-gradient fields.
  let M := smoothFCClass fullMemory (fun _ hk => hk) (E := E)
  let U := fun p => probedStepBasis M.policy (A p) (B p) g k
  let Z := fun p => probedImageBasis M.policy (A p) (B p) g k
  let C := fun p => pairModel (U p) (Z p)
  let G := fun p => probedGradient M.policy (A p) (B p) g (k+1)
  have hU : ContDiffAt ℝ 2 U x := smoothProbed_stepBasis_parametric M A B g x k hA hB Q hAx hBx hQ hpos hpre
  have hZ : ContDiffAt ℝ 2 Z x := smoothProbed_imageBasis_parametric M A B g x k hA hB Q hAx hBx hQ hpos hpre
  have hC (i j : Fin (k+1)) : ContDiffAt ℝ 2 (fun p => C p i j) x :=
    (contDiffAt_pi.mp hU (max i j)).inner ℝ (contDiffAt_pi.mp hZ (min i j))
  have hG : ContDiffAt ℝ 2 G x := smoothProbed_gradient_regular M.policy M.consistent A B (fun _ => g) x (k+1)
    hA hB contDiffAt_const Q hAx hBx hQ hpos hpre (M.smooth Q hQ hpos g (k+1) hpre)
  -- True quadratic model positivity derives the actual inverse domain without assuming global CG consistency of the targeted method.
  have hdet : (C x).det≠0 := by
    have hp : (C x).PosDef := by
      dsimp only [C,U,Z]
      rw [hAx,hBx]
      exact quadratic_probedModel_posDef M.policy M.consistent Q hQ hpos g k hpre
    exact hp.det_pos.ne'
  -- Identify the actual raw target query before applying genuine output regularity.
  have he : (fun p => probedGradient (targetedFinalMethod (k+1) target) (A p) (B p) g (k+1))=
      fun p => targetModelOutput (U p) (C p) (B p k) (G p) target := by
    funext p
    exact targetedFinalMethod_gradient_coordinates k target (A p) (B p) g
  rw [he]
  exact targetModelOutput_contDiffAt U C (fun p => B p k) G target x 2
    (fun i => contDiffAt_pi.mp hU i) hC (hB k (by omega)) hG hdet
end
end krylov.Envelope
