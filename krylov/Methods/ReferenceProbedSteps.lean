import krylov.Methods.ExecutedProbed
import krylov.Methods.QuadraticConsistency

/-!
Article: main_krylov, def:classes and prop:conv, actual generic probed reference steps.
Use: identify the genuine recorded quadratic reference displacement of every
CG-consistent probed policy with its true CG step, including stopped tails
and arbitrary finite zero correction traces.
Source: actual complete quadratic gradient consistency, real zero-query
correction execution and exact direction-scale cancellation in line search.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual CG-consistent probed method records precisely the genuine CG physical step on a true positive quadratic reference.
Use: Every actual CG-consistent probed method records precisely the genuine CG physical step on a true positive quadratic reference.
Article: main_krylov, def:classes and prop:conv, actual generic probed reference steps.
Proof: Its real correction movement is zero on the genuine quadratic history. Actual gradient consistency and the true positive CG direction scale reduce the executed search displacement to the real CG step. -/
theorem quadratic_probedStep_eq_cg (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (k : ℕ) : probedStep m (fun _ => Q) (fun _ => Q) g k=referenceStep Q g k := by
  -- Remove the genuine zero correction movement before cancelling the actual reference direction scale.
  let H := methodRun m (fun _ => Q) (fun _ => Q) g k
  obtain ⟨c,hc,hd,hzero⟩ := hm Q hQ hpos g k
  have hmove := (zeroCorrections_change_operator _ Q Q _ hzero).2.1
  change (probedPhase m (fun _ => Q) (fun _ => Q) g k).movement=0 at hmove
  rw [probedStep,hmove,add_zero]
  change lineLength H.gradient (m.direction H) (Q (m.direction H)) • m.direction H=_
  rw [hd,map_smul,quadratic_gradient_eq_cg m hm Q hQ hpos g k,lineStep_smul _ _ _ hc.ne']
  rfl
end
end krylov.Methods
