import krylov.Correction.GatedWindowPhase
import krylov.Methods.DirectionReindex
import Mathlib.Data.Fin.Rev

/-!
Article: main_krylov, thm:UCq, chronological coordinates of true observed solves.
Use: Relate the original newest-first full history to chronological actual
step and measured-secant arrays in the uniform stability induction.
Source: the existing exact executed-pair dictionary and bijective finite reindexing.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original newest-first observed-window direction is exactly its chronological finite-array solve.
Use: Connect original observed histories to the quantitative uniform induction.
Article: main_krylov, thm:UCq.
Proof: The existing genuine age-coordinate dictionary followed by the reversal permutation preserves the actual computed direction, including totalized singular data.
-/
theorem windowDirection_chronological (s y : ℕ → E) (g : E) (k : ℕ) :
    windowDirection (executedPairs s y k) g=
      conjugacyDirection (fun i : Fin k => s i.val) (fun i : Fin k => y i.val) g := by
  rw [windowDirection_executed]
  have he (i : Fin k) : k-1-i.val=(Fin.revPerm i).val := by simp only [Fin.revPerm_apply,Fin.rev,Fin.val_mk]; omega
  have hs : (fun i : Fin k => s (k-1-i.val))=(fun i : Fin k => s i.val) ∘ Fin.revPerm := by funext i; rw [he]; rfl
  have hy : (fun i : Fin k => y (k-1-i.val))=(fun i : Fin k => y i.val) ∘ Fin.revPerm := by funext i; rw [he]; rfl
  rw [hs,hy,conjugacyDirection_reindex]

/-- The actual full-history observed conjugacy determinant equals its chronological real step/secant determinant.
Use: Connect original observed histories to the quantitative uniform induction.
Article: main_krylov, thm:UCq.
Proof: Substitute the genuine complete executed transcript and simultaneously reverse both actual finite matrix axes. The true determinant is unchanged.
-/
theorem full_probed_observed_solve_chronological (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (crossGram (windowImages (selectedWindow fullMemory (methodRun m A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun m A B g k)))).det=
      (crossGram (fun i : Fin k => probedSecant m A B g i.val)
        (fun i : Fin k => probedStep m A B g i.val)).det := by
  rw [fullWindow_methodRun,crossGram_executed_det]
  have he (i : Fin k) : k-1-i.val=(Fin.revPerm i).val := by simp only [Fin.revPerm_apply,Fin.rev,Fin.val_mk]; omega
  have hm : crossGram (fun i : Fin k => probedSecant m A B g (k-1-i.val))
      (fun i : Fin k => probedStep m A B g (k-1-i.val))=
      (crossGram (fun i : Fin k => probedSecant m A B g i.val)
        (fun i : Fin k => probedStep m A B g i.val)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [crossGram,Matrix.submatrix,he]
    rfl
  rw [hm,Matrix.det_submatrix_equiv_self]

end
end krylov.Methods
