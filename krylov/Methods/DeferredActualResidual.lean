import krylov.Methods.DeferredLastPairing
import krylov.Methods.CorrectionFreeOracles

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual executed final deferred residual transfer.
Use: identify every genuine real old-step/final-gradient residual with
its true fresh segment defect and actual unresolved previous residual.
Source: genuine final deferred observed secant equations, actual correction-free
secant/search/recorded-step identities and true old segment symmetry.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuinely executed final deferred step satisfies the exact true fresh-defect plus old-residual damping identity for every actual earlier recorded step.
Use: The genuinely executed final deferred step satisfies the exact true fresh-defect plus old-residual damping identity for every actual earlier recorded step.
Article: main_krylov, apB:lem:mu(d), actual executed final deferred residual transfer.
Proof: Use the actual recorded secant and genuine symmetric old segment to read the real tilted direction equation; the true empty-correction searched gradient and real last recorded line step give the exact actual residual transfer. -/
theorem deferredMethod_last_residual (a : ℝ) (A B : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k)
    (hAi : (A i).toLinearMap.IsSymmetric)
    (hdet : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (methodRun (deferredMethod fullMemory (k+1) a) A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun (deferredMethod fullMemory (k+1) a) A B g k)))).det) :
    let m := deferredMethod fullMemory (k+1) a
    let α := lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k)
    inner ℝ (probedStep m A B g i) (probedGradient m A B g (k+1))=
      inner ℝ (probedStep m A B g i) ((A k-A i) (probedStep m A B g k))+
        (1-α/a)*inner ℝ (probedStep m A B g i) (probedGradient m A B g k) := by
  -- Read the true earlier recorded secant equation and genuine old segment action from the actual executed method.
  let m := deferredMethod fullMemory (k+1) a (E := E)
  have hm : CorrectionFree m := deferredMethod_correctionFree fullMemory (k+1) a
  have hp := deferredMethod_last_secant_pairing a A B g k i hi hdet
  rw [correctionFree_secant m hm] at hp
  have hs := hAi (probedStep m A B g i) (probedDirection m A B g k)
  change inner ℝ (A i (probedStep m A B g i)) (probedDirection m A B g k)=
    inner ℝ (probedStep m A B g i) (A i (probedDirection m A B g k)) at hs
  rw [hs] at hp
  -- The real scalar residual identity is proved on abstract physical vectors before substituting genuine execution fields.
  have htransfer (s v d : E) (α : ℝ)
      (hp : inner ℝ s (A i d)= -a⁻¹*inner ℝ s v) :
      inner ℝ s (v+α • A k d)=inner ℝ s ((A k-A i) (α • d))+(1-α/a)*inner ℝ s v := by
    simp only [inner_add_right,real_inner_smul_right,_root_.sub_apply,map_smul,inner_sub_right,hp]
    ring
  dsimp only
  rw [correctionFree_gradient_succ m hm A B g k,correctionFree_step m hm A B g k]
  exact htransfer (probedStep m A B g i) (probedGradient m A B g k)
    (probedDirection m A B g k)
    (lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k)) hp
end
end krylov.Methods
