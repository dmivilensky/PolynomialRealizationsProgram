import krylov.Envelope.TargetedGradientRegularity

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine targeted output derivative cancellation.
Use: prove that every actual full reference-model coordinate of the true targeted final-gradient derivative vanishes.
Source: actual primitive-derived FC model fields, genuine positive reference model domains and the real C-one target-model first-jet theorem.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability Matrix
open scoped Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual FC reference-model basis vector is orthogonal to the genuine targeted output derivative on every real smooth operator path through the chosen reference.
Use: Every actual FC reference-model basis vector is orthogonal to the genuine targeted output derivative on every real smooth operator path through the chosen reference.
Article: main_krylov, apB:prop:consist, genuine targeted output derivative cancellation.
Proof: Derive the actual incoming FC and full-model fields, prove their real reference domains, identify the genuinely executed target query and apply the true target-model cancellation. -/
theorem targeted_gradient_deriv_orthogonal
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (hA : ∀ i<k+1,ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<k+1,ContDiffAt ℝ 2 (fun t => B t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) (j : Fin (k+1)) :
    inner ℝ (probedStepBasis (fcMethod fullMemory) (fun _ => Q) (fun _ => Q) g k j)
      (deriv (fun t => probedGradient (targetedFinalMethod (k+1) (CG.gradient Q g (k+1))) (A t) (B t) g (k+1)) 0)=0 := by
  -- Derive the real FC prefix fields and genuine target gradient from the actual primitive smooth implementation.
  let M := smoothFCClass fullMemory (fun _ hk => hk) (E := E)
  let U := fun t => probedStepBasis M.policy (A t) (B t) g k
  let Z := fun t => probedImageBasis M.policy (A t) (B t) g k
  let C := fun t => pairModel (U t) (Z t)
  let G := fun t => probedGradient M.policy (A t) (B t) g (k+1)
  have hU := smoothProbed_stepBasis_parametric M A B g 0 k hA hB Q hA0 hB0 hQ hpos hpre
  have hZ := smoothProbed_imageBasis_parametric M A B g 0 k hA hB Q hA0 hB0 hQ hpos hpre
  have hC (i l : Fin (k+1)) : ContDiffAt ℝ 2 (fun t => C t i l) 0 :=
    (contDiffAt_pi.mp hU (max i l)).inner ℝ (contDiffAt_pi.mp hZ (min i l))
  have hG : ContDiffAt ℝ 2 G 0 := smoothProbed_gradient_regular M.policy M.consistent A B (fun _ => g) 0 (k+1)
    hA hB contDiffAt_const Q hA0 hB0 hQ hpos hpre (M.smooth Q hQ hpos g (k+1) hpre)
  have hU0 : U 0=probedStepBasis M.policy (fun _ => Q) (fun _ => Q) g k := by dsimp only [U];rw [hA0,hB0]
  have hZ0 : Z 0=probedImageBasis M.policy (fun _ => Q) (fun _ => Q) g k := by dsimp only [Z];rw [hA0,hB0]
  have hG0 : G 0=CG.gradient Q g (k+1) := by
    dsimp only [G]
    rw [hA0,hB0]
    exact quadratic_gradient_eq_cg M.policy M.consistent Q hQ hpos g (k+1)
  -- The actual full reference model is positive and exactly equals the genuine correction compression.
  have hdet : (C 0).det≠0 := by
    have hp : (C 0).PosDef := by
      dsimp only [C]
      rw [hU0,hZ0]
      exact quadratic_probedModel_posDef M.policy M.consistent Q hQ hpos g k hpre
    exact hp.det_pos.ne'
  have hmodel : correctionCompression (U 0) (B 0 k)=C 0 := by
    dsimp only [C]
    rw [hB0,hU0,hZ0,quadratic_imageBasis,pairModel_quadratic _ Q hQ]
  -- Transfer the proved genuine target-model derivative cancellation to the actual raw executed output.
  have he : (fun t => probedGradient (targetedFinalMethod (k+1) (CG.gradient Q g (k+1))) (A t) (B t) g (k+1))=
      fun t => targetModelOutput (U t) (C t) (B t k) (G t) (CG.gradient Q g (k+1)) := by
    funext t
    exact targetedFinalMethod_gradient_coordinates k _ (A t) (B t) g
  rw [he]
  change inner ℝ (probedStepBasis M.policy (fun _ => Q) (fun _ => Q) g k j) _=0
  rw [← hU0]
  exact targetModelOutput_projected_deriv_zero U C (fun t => B t k) G _
    (fun i => (contDiffAt_pi.mp hU i).of_le (by norm_num)) (fun i l => (hC i l).of_le (by norm_num))
    ((hB k (by omega)).of_le (by norm_num)) (hG.of_le (by norm_num)) hdet hmodel hG0 j
end
end krylov.Envelope
