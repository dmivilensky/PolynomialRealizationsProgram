import krylov.Methods.ProbedModelReference
import krylov.Envelope.ModelCorrectionFirstJet
import krylov.Methods.FinalizedSmoothClass

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(a), actual final Galerkin projection first jets.
Use: prove that appending the real latest-model solve to any genuine smooth
source method annihilates every true full-basis residual first derivative.
Source: actual primitive source coefficient regularity, genuine full-model
reference positivity and the proved real C-one correction normal equation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine appended latest-model solve makes every actual full-step-basis final-gradient residual derivative zero for every smooth source-class method.
Use: The genuine appended latest-model solve makes every actual full-step-basis final-gradient residual derivative zero for every smooth source-class method.
Article: main_krylov, apB:lem:mu(a), actual final Galerkin projection first jets.
Proof: Derive real basis, observed model and incoming-gradient C-two regularity and the true positive quadratic model domain. The actual wrapper output equals the real one-model correction; its zero reference right-hand side and zero reference model error make every genuine projected residual derivative vanish. -/
theorem finalized_projected_residual_deriv_zero (M : SmoothProbedClass E)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (hA : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1, CG.gradient Q g i≠0) (j : Fin (k+1)) :
    deriv (fun t => inner ℝ (probedStepBasis M.policy (A t) (B t) g k j)
      (probedGradient (finalizedMethod M.policy (k+1)) (A t) (B t) g (k+1))) 0=0 := by
  -- All model columns, observations and the incoming gradient are from the genuine original executed method.
  let U := fun t => probedStepBasis M.policy (A t) (B t) g k
  let Z := fun t => probedImageBasis M.policy (A t) (B t) g k
  let C := fun t => pairModel (U t) (Z t)
  let G := fun t => probedGradient M.policy (A t) (B t) g (k+1)
  have hs := M.smooth Q hQ hpos g (k+1) hpre
  have hU : ContDiffAt ℝ 2 U 0 := smoothProbed_stepBasis_regular M.policy M.consistent A B (fun _ => g) (k+1)
    hA hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hs k (by omega)
  have hZ : ContDiffAt ℝ 2 Z 0 := smoothProbed_imageBasis_regular M A B g k hA hB Q hA0 hB0 hQ hpos hpre
  have hC (i l : Fin (k+1)) : ContDiffAt ℝ 2 (fun t => C t i l) 0 :=
    (contDiffAt_pi.mp hU (max i l)).inner ℝ (contDiffAt_pi.mp hZ (min i l))
  have hG : ContDiffAt ℝ 2 G 0 := smoothProbed_gradient_regular M.policy M.consistent A B (fun _ => g) 0 (k+1)
    hA hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hs
  have hU0 : U 0=probedStepBasis M.policy (fun _ => Q) (fun _ => Q) g k := by
    dsimp only [U]
    rw [hA0,hB0]
  have hZ0 : Z 0=probedImageBasis M.policy (fun _ => Q) (fun _ => Q) g k := by
    dsimp only [Z]
    rw [hA0,hB0]
  have hG0 : G 0=CG.gradient Q g (k+1) := by
    dsimp only [G]
    rw [hA0,hB0]
    exact quadratic_gradient_eq_cg M.policy M.consistent Q hQ hpos g (k+1)
  -- Actual global CG consistency gives the true positive model and genuine zero reference projected right-hand side.
  have hdet : (C 0).det≠0 := by
    have hp : (C 0).PosDef := by
      dsimp only [C]
      rw [hU0,hZ0]
      exact quadratic_probedModel_posDef M.policy M.consistent Q hQ hpos g k hpre
    exact hp.det_pos.ne'
  have hmodel : correctionCompression (U 0) (B 0 k)=C 0 := by
    dsimp only [C]
    rw [hB0,hU0,hZ0,quadratic_imageBasis,pairModel_quadratic _ Q hQ]
  have hρ : coordinates (U 0) (G 0)=0 := by
    rw [hU0,hG0]
    exact quadratic_stepBasis_coordinates_final M.policy M.consistent Q hQ hpos g k hpre
  -- Identify the real appended-query output before applying the genuine C-one normal-equation derivative cancellation.
  have he (t : ℝ) : probedGradient (finalizedMethod M.policy (k+1)) (A t) (B t) g (k+1)=
      G t+B t k (combine (U t) (modelCoefficients (U t) (C t) (G t))) := by
    rw [finalizedMethod_gradient_last,latestAfter_coordinates]
    rfl
  simp_rw [he]
  exact modelCorrection_projected_deriv_zero U C (fun t => B t k) G
    (fun i => (contDiffAt_pi.mp hU i).of_le (by norm_num)) (fun i l => (hC i l).of_le (by norm_num))
    ((hB k (by omega)).of_le (by norm_num)) (hG.of_le (by norm_num)) hdet hmodel hρ j
end
end krylov.Envelope
