import krylov.Methods.OracleCost

/-!
Article: main_krylov, alg:fc, actual RFC final-output execution and cost.
Use: instantiate the output-aware correction protocol with the real observed
RFC gate/model and compare its actual output and cost with ordinary evaluation.
Source: the final correction is observed only when another solve follows.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual terminal RFC correction rule with the real observed gate and an unevaluated last correction.
Use: every needed intermediate gradient is genuinely queried; the final returned point has no gradient observation.
Article: main_krylov, alg:fc, observe unless returning the final point. -/
def rfcFinalPhase (memory : ℕ → ℕ) (count : ℕ) (H : History E) (z : E) : FinalCorrectionTree E :=
  let W := selectedWindow memory H
  let d := windowDirection W H.gradient
  let U := (d,z)::W
  if W≠[] ∧ ‖windowDefect W‖<1 then
    repeatedModelFinal (windowSteps U) (windowModel U) count (searchedGradient H.gradient d z)
  else .output 0

/-- The actual terminal RFC correction phase preserves the exact fully evaluated physical movement and semantic gradient.
Use: the protocol's omitted last observation changes neither the final mathematical point nor its gradient.
Article: main_krylov, alg:fc and def:classes(M), actual final output.
Proof: both real gate branches agree; in the accepted branch the already
proved actual repeated-model output-elision theorem applies, including zero prescribed corrections. -/
theorem rfcFinalPhase_exact (memory : ℕ → ℕ) (count : ℕ) (H : History E) (z : E) (B : E →L[ℝ] E) :
    let g := searchedGradient H.gradient (windowDirection (selectedWindow memory H) H.gradient) z
    let r := runFinalCorrections (rfcFinalPhase memory count H z) B g
    let q := runCorrections (rfcCorrection memory count H z) B g
    r.movement+r.output=q.movement ∧ r.gradient+B r.output=q.gradient := by
  -- The real observed-data gate and the actual augmented model are identical in both executions.
  unfold rfcFinalPhase rfcCorrection
  dsimp only
  split
  · cases count with
    | zero => simp only [repeatedModelFinal,runFinalCorrections,repeatedModelTree,runCorrections,
        map_zero,add_zero,and_self]
    | succ c => exact (repeatedModelFinal_exact _ _ B c _).imp_right And.left
  · simp only [runFinalCorrections,runCorrections,map_zero,add_zero,and_self]

/-- The terminal RFC phase queries exactly count−1 corrections when its actual gate passes, and zero otherwise.
Use: count one is a completely unevaluated final correction, while all later solves still have their required observations.
Article: main_krylov, def:classes(M), final-output gradient count.
Proof: inspect the real observed gate; the accepted repeated-model transcript has exactly one fewer query when the count is positive. -/
theorem rfcFinalPhase_count (memory : ℕ → ℕ) (count : ℕ) (H : History E) (z : E) (B : E →L[ℝ] E) :
    let g := searchedGradient H.gradient (windowDirection (selectedWindow memory H) H.gradient) z
    (runFinalCorrections (rfcFinalPhase memory count H z) B g).trace.length=
      if selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1 then count-1 else 0 := by
  unfold rfcFinalPhase
  dsimp only
  split
  · cases count with
    | zero => rfl
    | succ c => exact repeatedModelFinal_count _ _ B c _
  · rfl

/-- The actual final-output-aware RFC iteration returns exactly the fully evaluated physical point and semantic gradient.
Use: the real algorithm may return its terminal point while leaving its gradient unobserved.
Article: main_krylov, alg:fc, real unevaluated final point.
Proof: the true line probe and line movement agree in both executions;
the real gated correction-elision identity identifies the remaining physical displacement and semantic gradient. -/
theorem rfcFinal_output_exact (memory : ℕ → ℕ) (count : ℕ) (A B : E →L[ℝ] E) (H : History E) :
    let m := rfcMethod memory count
    let d := m.direction H
    let z := A d
    let g := searchedGradient H.gradient d z
    let r := runFinalCorrections (rfcFinalPhase memory count H z) B g
    H.displacement+lineLength H.gradient d z • d+r.movement+r.output=(methodAdvance m A B H).displacement ∧
      r.gradient+B r.output=(methodAdvance m A B H).gradient := by
  -- The final physical output includes the last data-only displacement without inserting an observation record.
  have he := rfcFinalPhase_exact memory count H (A ((rfcMethod memory count).direction H)) B
  dsimp only [rfcMethod,retainedMethod] at he ⊢
  constructor
  · change H.displacement+_+_+_=(_+_)+H.displacement
    rw [add_assoc,he.1]
    abel
  · exact he.2

/-- The actual RFC final-output execution saves exactly one gradient when its real gate accepts a positive number of corrections.
Use: combines the complete real prefix cost, the one final probe and the exact terminal correction trace.
Article: main_krylov, def:classes(M) and alg:fc, full oracle accounting.
Proof: substitute the two real gate-dependent correction transcript lengths
into the exact actual iteration cost; elementary counting handles both the skipped and zero-count cases. -/
theorem rfcFinal_cost_exact (memory : ℕ → ℕ) (count : ℕ) (A B : E →L[ℝ] E) (H : History E) :
    let m := rfcMethod memory count
    let d := m.direction H
    let g := searchedGradient H.gradient d (A d)
    let r := runFinalCorrections (rfcFinalPhase memory count H (A d)) B g
    probedCost H+1+r.trace.length+
      (if (selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) ∧ 0<count then 1 else 0)=
      probedCost (methodAdvance m A B H) := by
  -- This counts only actual queries, with the final returned correction deliberately absent from the observed trace.
  dsimp only
  rw [probedCost_advance]
  dsimp only [rfcMethod,retainedMethod]
  rw [rfcFinalPhase_count,rfcCorrection_count]
  by_cases hp : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1
  · simp only [ite_eq_left hp]
    by_cases hc : 0<count
    · rw [ite_eq_left ⟨hp,hc⟩]
      omega
    · rw [ite_eq_right (fun h => hc h.2)]
      omega
  · have hp' : ¬((selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) ∧ 0<count) :=
      fun h => hp h.1
    simp only [ite_eq_right hp,ite_eq_right hp',Nat.add_zero]

end
end krylov.Methods
