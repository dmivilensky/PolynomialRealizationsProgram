import bezout.Algorithms.PolynomialExecution
import bezout.Comparisons.Competitors.Linear
import Mathlib.Data.Fin.VecNotation

/-!
Article: bezout, Equations `eq:competitor-momentum` and `eq:competitor-transfer`.
Use: literal momentum, extrapolated queries and prescribed stage resets are
actual one-call physical programs, for every oracle answer stream.
Proof: in-place state assignments expose the physical query and the two-by-two
spectral propagation; the general tape theorem identifies their causal history.
-/

namespace bezout.Comparisons.Competitors
noncomputable section
open scoped BigOperators Matrix
open bezout.Algorithms

/-- Literal coefficients of a finite momentum competitor.
The previous state is reset only at the prescribed stage starts. -/
structure Momentum where
  alpha : ℕ → ℝ
  beta : ℕ → ℝ
  extrapolated : Bool
  reset : ℕ → Bool

namespace Momentum

/-- Three physical slots are current, previous and query/answer workspace.
The new current overwrites previous, followed by a pointer swap. -/
def program (data : Momentum) (N : ℕ) : RegisterProgram 3 N where
  initial := ![1,1,0]
  before s :=
    (if data.reset s.val then [.assign 1 ![1,0,0]] else []) ++
    [.assign 2 (if data.extrapolated then ![1+data.beta s.val,-data.beta s.val,0]
      else ![1,0,0])]
  queryRegister _ := 2
  answerRegister _ := 2
  after s :=
    [.assign 1 ![1+data.beta s.val,-data.beta s.val,-data.alpha s.val],
      .permute (Equiv.swap 0 1)]
  outputRegister := 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The previous state after a prescribed reset. -/
def previous (data : Momentum) (s : ℕ) (current previous : E) : E :=
  if data.reset s then current else previous

/-- The exact physical query: the current state or the specified extrapolation. -/
def query (data : Momentum) (s : ℕ) (current previous : E) : E :=
  if data.extrapolated then
    (1+data.beta s) • current-data.beta s • data.previous s current previous else current

/-- The physical in-place query preparation, including a reset before the call. -/
theorem before_vectors (data : Momentum) (N : ℕ) (s : Fin N) (x p a : E) :
    executeLinear ((data.program N).before s) ![x,p,a] =
      ![x, data.previous s.val x p, data.query s.val x p] := by
  cases he : data.extrapolated <;> cases hr : data.reset s.val <;>
    ext i <;> fin_cases i <;>
    simp [program, previous, query, he, hr, executeLinear, LinearInstruction.execute,
      combination, Fin.sum_univ_succ, sub_eq_add_neg]

/-- One physical momentum stage uses exactly its actual oracle answer. -/
theorem stage_vectors (data : Momentum) (N : ℕ) (s : Fin N)
    (oracle : Fin N → E → E) (x p a : E) (calls : ℕ) :
    ((data.program N).stage oracle s ⟨![x,p,a],calls⟩).vectors =
      ![(1+data.beta s.val) • x-data.beta s.val • data.previous s.val x p-
          data.alpha s.val • oracle s (data.query s.val x p),
        x, oracle s (data.query s.val x p)] := by
  rw [RegisterProgram.stage, data.before_vectors]
  ext i
  fin_cases i <;>
    simp [program, executeLinear, LinearInstruction.execute, combination,
      Fin.sum_univ_succ, Equiv.swap_apply_def, sub_eq_add_neg, add_assoc]

/-- The actual prepared query depends only on the two live state components. -/
theorem queryAt_eq (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) (s : Fin N) :
    (data.program N).queryAt oracle initial s =
      data.query s.val (((data.program N).runPrefix oracle initial s.val).vectors 0)
        (((data.program N).runPrefix oracle initial s.val).vectors 1) := by
  let v := ((data.program N).runPrefix oracle initial s.val).vectors
  have hv : v = ![v 0,v 1,v 2] := by ext i; fin_cases i <;> rfl
  change executeLinear _ v _ = _
  rw [hv, data.before_vectors]
  rfl

/-- Zero oracle answers preserve the initial point in both state slots. -/
theorem zero_tape (data : Momentum) (N k : ℕ) (hk : k≤N) :
    (data.program N).runTape (1:ℝ) (fun _ => 0) k = ![1,1,0] := by
  induction k with
  | zero => ext i; fin_cases i <;>
      simp [RegisterProgram.runTape, RegisterProgram.runPrefix, RegisterProgram.initialState, program]
  | succ k ih =>
    rw [RegisterProgram.runTape_succ _ _ _ k (show k<N by omega), ih (by omega)]
    change ((data.program N).stage (RegisterProgram.tapeOracle (fun _ => (0:ℝ)))
      ⟨k,by omega⟩ ⟨![1,1,0],k⟩).vectors = _
    rw [data.stage_vectors]
    simp [RegisterProgram.tapeOracle, previous, smul_eq_mul]

/-- Momentum and reset programs are normalized actual causal histories. -/
theorem normalized (data : Momentum) (N : ℕ) : (data.program N).TranslationNormalized where
  query s := by
    rw [RegisterProgram.queryCoefficient_initial_value, data.zero_tape N s.val (Nat.le_of_lt s.isLt)]
    rw [data.before_vectors]
    cases he : data.extrapolated <;> cases hr : data.reset s.val <;>
      simp [program, query, previous, he, hr, smul_eq_mul]
  output := by
    unfold RegisterProgram.outputCoefficient
    rw [RegisterProgram.coefficientState_initial_value, data.zero_tape N N le_rfl]
    rfl

/-- The actual causal history of the literal finite momentum configuration. -/
def history (data : Momentum) (N : ℕ) : bezout.History N :=
  (data.program N).history (data.normalized N)

/-- Complete query-stream equivalence for every time-dependent oracle. -/
theorem query_eq_history (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) (s : Fin N) :
    (data.program N).queryAt oracle initial s =
      (data.history N).oracleQuery initial oracle s :=
  RegisterProgram.query_eq_history _ _ initial oracle s

/-- Complete physical-output equivalence, without a noiseless restriction. -/
theorem output_eq_history (data : Momentum) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) :
    (data.program N).output oracle initial = (data.history N).oracleOutput initial oracle :=
  RegisterProgram.output_eq_history _ _ initial oracle

/-- The prescribed finite horizon is exactly the number of physical calls. -/
theorem oracle_calls (data : Momentum) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    ((data.program N).run oracle initial).calls=N := RegisterProgram.run_calls _ _ _

/-- Resetting the previous state is right multiplication by the printed J. -/
def resetMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,0]

/-- The literal spectral momentum matrix, before its optional reset. -/
def baseMatrix (data : Momentum) (s : ℕ) (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if data.extrapolated then
    !![(1-data.alpha s*lam)*(1+data.beta s), -(1-data.alpha s*lam)*data.beta s; 1,0]
  else !![1+data.beta s-data.alpha s*lam, -data.beta s; 1,0]

/-- The printed two-by-two propagation including a right-multiplied reset. -/
def matrix (data : Momentum) (s : ℕ) (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  data.baseMatrix s lam * if data.reset s then resetMatrix else 1

end Momentum
end
end bezout.Comparisons.Competitors
