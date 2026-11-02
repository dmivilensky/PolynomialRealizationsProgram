import krylov.Methods.CorrectionFree
import krylov.Methods.SmoothProbedFields

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, actual correction-free oracle identities.
Use: remove unused genuine correction operators and identify the true
recorded secants, line steps and actual returned gradients without corrections.
Source: genuine raw complete-history execution and the proved actual
secant defect identity with real zero correction movements.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual correction-free policy has exactly the same genuine complete history for all real correction-operator sequences.
Use: Every actual correction-free policy has exactly the same genuine complete history for all real correction-operator sequences.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, actual correction-free oracle identities.
Proof: Induct over the true empty correction execution; no actual correction oracle action enters any genuine observation. -/
theorem correctionFree_run_independent (m : ProbedMethod E) (hm : CorrectionFree m)
    (A B C : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    methodRun m A B g k=methodRun m A C g k := by
  -- Real complete histories retain the same genuine observations because every actual correction tree is empty.
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih]
    unfold methodAdvance
    dsimp only
    rw [hm]
    rfl

/-- Every genuine correction-free recorded secant is the actual line operator applied to its true recorded step.
Use: Every genuine correction-free recorded secant is the actual line operator applied to its true recorded step.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, actual correction-free oracle identities.
Proof: The actual secant defect is the real operator mismatch applied to the genuine zero correction movement. -/
theorem correctionFree_secant (m : ProbedMethod E) (hm : CorrectionFree m)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedSecant m A B g k=A k (probedStep m A B g k) := by
  have he := probedSecant_defect_identity m A B g k
  have hz : (probedPhase m A B g k).movement=0 := by
    unfold probedPhase
    dsimp only
    rw [hm]
    rfl
  rw [hz,map_zero] at he
  exact sub_eq_zero.mp he

/-- Every actual correction-free recorded step is exactly its genuine observed exact-search scalar times its true direction.
Use: Every actual correction-free recorded step is exactly its genuine observed exact-search scalar times its true direction.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, actual correction-free oracle identities.
Proof: The real correction movement is zero. -/
theorem correctionFree_step (m : ProbedMethod E) (hm : CorrectionFree m)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedStep m A B g k=
      lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k) •
        probedDirection m A B g k := by
  change _+_=_
  have hz : (probedPhase m A B g k).movement=0 := by
    unfold probedPhase
    dsimp only
    rw [hm]
    rfl
  rw [hz,add_zero]
  rfl

/-- The actual next correction-free gradient is the genuine searched gradient from the true current gradient, direction and observed probe.
Use: The actual next correction-free gradient is the genuine searched gradient from the true current gradient, direction and observed probe.
Article: main_krylov, apB:lem:mu(d) and s3:thm:cf, actual correction-free oracle identities.
Proof: The real empty correction phase returns its genuine input searched gradient unchanged. -/
theorem correctionFree_gradient_succ (m : ProbedMethod E) (hm : CorrectionFree m)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedGradient m A B g (k+1)=searchedGradient
      (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k) := by
  rw [probedGradient_succ]
  unfold probedPhase
  dsimp only
  rw [hm]
  rfl

end
end krylov.Methods
