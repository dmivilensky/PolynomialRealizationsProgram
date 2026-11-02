import krylov.Methods.RFCS
import krylov.Methods.ExecutedProbed
import krylov.Methods.SmoothProbedFields
import krylov.Stability.RetainedPhase

/-!
Article: main_krylov, thm:RFCS, actual secant-probed RFC execution.
Use: distinguish the measured probe from the real line and correction
segments throughout the genuine observed history and final residual.
Source: the actual RFC-S executor, real retained finite pair arrays and
proved positive-quadratic model/search/gate domains.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual observed RFC-S gradient after its genuine independent-probe iterations.
Use: all error statements refer to real evaluated gradients.
Article: main_krylov, thm:RFCS, true independent-probe execution fields. -/
def rfcSGradient (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  (rfcSRun memory Ap A B g k).gradient

/-- The true data-only retained direction selected from the genuine RFC-S observed history.
Use: the independent-probe protocol uses its own actual measured secants.
Article: main_krylov, thm:RFCS, true independent-probe execution fields. -/
def rfcSDirection (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  let H := rfcSRun memory Ap A B g k
  windowDirection (selectedWindow memory H) H.gradient

/-- The actual line displacement predicted from the genuine secant probe.
Use: keep the true predicted search displacement distinct from the full evaluated step.
Article: main_krylov, thm:RFCS, true independent-probe execution fields. -/
def rfcSLineStep (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  let d := rfcSDirection memory Ap A B g k
  lineLength (rfcSGradient memory Ap A B g k) d (Ap k d) • d

/-- The genuine one-query predicted-gradient model correction phase used by the actual RFC-S executor.
Use: separate the model prediction from the physically evaluated line mismatch.
Article: main_krylov, thm:RFCS, true independent-probe execution fields. -/
def rfcSPhase (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : CorrectionResult E :=
  let H := rfcSRun memory Ap A B g k
  let d := rfcSDirection memory Ap A B g k
  let z := Ap k d
  runCorrections (rfcCorrection memory 1 H z) (B k) (searchedGradient H.gradient d z)

/-- The true total evaluated RFC-S displacement, including its actual predicted-model correction movement.
Use: record the genuine physical step in the measured secant history.
Article: main_krylov, thm:RFCS, true independent-probe execution fields. -/
def rfcSStep (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  rfcSLineStep memory Ap A B g k+(rfcSPhase memory Ap A B g k).movement

/-- The actual consecutive evaluated-gradient difference recorded by the RFC-S executor.
Use: measured pairs contain the real physical secant rather than a probe prediction.
Article: main_krylov, thm:RFCS, true independent-probe execution fields. -/
def rfcSSecant (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  rfcSGradient memory Ap A B g (k+1)-rfcSGradient memory Ap A B g k

/-- The actual RFC-S output is the genuinely executed predicted-model correction result plus exactly the original probe-to-line mismatch on the actual line displacement.
Use: only the real final probe mismatch can survive the full terminal model correction at first order.
Article: main_krylov, thm:RFCS, exact actual independent-probe identity.
Proof: unfold the two actual gate branches. The real line contribution differs from its prediction by precisely the displayed operator difference; the physical correction contribution is identical. -/
theorem rfcSGradient_succ (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    rfcSGradient memory Ap A B g (k+1)=
      (rfcSPhase memory Ap A B g k).gradient+(A k-Ap k) (rfcSLineStep memory Ap A B g k) := by
  unfold rfcSGradient rfcSRun rfcSAdvance rfcSPhase rfcSDirection rfcSLineStep rfcCorrection
  dsimp only
  split <;> simp only [repeatedModelTree,runCorrections,searchedGradient,map_smul,_root_.sub_apply,add_zero,rfcSGradient,rfcSDirection,History.gradient,smul_sub]
  all_goals abel

/-- The genuine RFC-S history contains exactly its true total steps and actually evaluated consecutive-gradient secants in chronological newest-first order.
Use: use fixed finite retained-history coordinates without replacing measured secants by hypothetical line images.
Article: main_krylov, thm:RFCS, exact actual independent-probe identity.
Proof: each original real iteration records the true total evaluated displacement and true next gradient. Prepending that actual pair preserves the genuine chronological executed-pair recursion. -/
theorem rfcSRun_pairs (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (rfcSRun memory Ap A B g k).pairs=executedPairs (rfcSStep memory Ap A B g) (rfcSSecant memory Ap A B g) k := by
  -- Prepend the actual original evaluated step and measured consecutive-gradient secant.
  induction k with
  | zero => rfl
  | succ k ih =>
    have hnext : (rfcSRun memory Ap A B g (k+1)).pairs=
        (rfcSStep memory Ap A B g k,rfcSSecant memory Ap A B g k)::(rfcSRun memory Ap A B g k).pairs := by
      simp only [rfcSStep,rfcSLineStep,rfcSPhase,rfcSDirection,rfcSSecant,rfcSGradient]
      rw [rfcSRun]
      unfold rfcSAdvance rfcCorrection
      dsimp only
      split_ifs <;> simp only [History.pairs,recordPairs,History.gradient,repeatedModelTree,runCorrections,add_zero]
    rw [hnext,ih]
    rfl


/-- An exact independent probe identifies every actual RFC-S gradient, raw direction, total step and measured secant with the original true RFC executor.
Use: discharge the independent-probe method's actual reference fields from the proved real quadratic run.
Article: main_krylov, thm:RFCS, exact actual independent-probe identity.
Proof: the original exact-probe transcript theorem identifies the genuine histories. Their actual direction, model correction and measured fields are then identical. -/
theorem rfcSFields_exact (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    rfcSGradient memory A A B g k=probedGradient (rfcMethod memory 1) A B g k ∧
    rfcSDirection memory A A B g k=probedDirection (rfcMethod memory 1) A B g k ∧
    rfcSStep memory A A B g k=probedStep (rfcMethod memory 1) A B g k ∧
    rfcSSecant memory A A B g k=probedSecant (rfcMethod memory 1) A B g k := by
  simp only [rfcSGradient,rfcSDirection,rfcSStep,rfcSLineStep,rfcSPhase,rfcSSecant,rfcSRun_exact]
  exact ⟨rfl,rfl,rfl,rfl⟩


/-- When the actual line and correction segments coincide, every genuinely recorded RFC-S secant is exactly that physical operator applied to the true total evaluated step.
Use: the independent probe introduces no fictitious inconsistency into the real measured source pairs.
Article: main_krylov, thm:RFCS, exact actual independent-probe identity.
Proof: use the exact actual output mismatch identity. The physical line and correction contributions share the same true operator, so their sum is its action on the actual recorded total step. -/
theorem rfcSSecant_exact_segment (memory : ℕ → ℕ) (Ap A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    rfcSSecant memory Ap A A g k=A k (rfcSStep memory Ap A A g k) := by
  -- The actual physical line and correction contributions share their true segment operator.
  unfold rfcSSecant
  rw [rfcSGradient_succ]
  unfold rfcSStep rfcSPhase rfcSLineStep rfcSDirection rfcSGradient rfcCorrection
  dsimp only
  split
  all_goals
    simp only [repeatedModelTree,runCorrections,searchedGradient,add_zero,map_add,map_smul,_root_.sub_apply,
      smul_sub]
    abel

end
end krylov.Methods
