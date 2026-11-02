import bezout.History.Execution

/-!
Article: bezout, Algorithms 1--2 (physical vector storage and oracle calls).
Use: explicit in-place linear assignments and register renamings describe
exact executions with four or six vector slots, including the oracle workspace.
Proof: the operational interpreter stores one vector per finite register and
executes one oracle call in each active stage. Counters are scalar ghost data.
-/

namespace bezout.Algorithms

open scoped BigOperators
noncomputable section

/-- A physical register instruction either overwrites one vector by a linear
combination of the current vectors or merely renames the register pointers.
Use: no uncounted vector-valued temporary occurs in the execution model. -/
inductive LinearInstruction (r : ℕ) where
  | assign (target : Fin r) (weights : Fin r → ℝ)
  | permute (order : Equiv.Perm (Fin r))

/-- A scalar linear combination of the current physical registers. -/
def combination {r : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (weights : Fin r → ℝ) (registers : Fin r → E) : E :=
  ∑ i, weights i • registers i

/-- Exact semantics of one in-place linear instruction.
Use: the right side is evaluated before its single target is overwritten. -/
def LinearInstruction.execute {r : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (instruction : LinearInstruction r) (registers : Fin r → E) : Fin r → E :=
  match instruction with
  | .assign target weights => Function.update registers target (combination weights registers)
  | .permute order => fun i => registers (order i)

/-- Execute a finite sequence of in-place vector assignments in printed order. -/
def executeLinear {r : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (instructions : List (LinearInstruction r)) (registers : Fin r → E) : Fin r → E :=
  instructions.foldl (fun state instruction => instruction.execute state) registers

/-- The empty instruction sequence preserves every physical register. -/
@[simp] theorem executeLinear_nil {r : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (registers : Fin r → E) : executeLinear [] registers = registers := rfl

/-- Instruction lists execute from the head, allowing induction on their printed order. -/
@[simp] theorem executeLinear_cons {r : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (instruction : LinearInstruction r) (rest : List (LinearInstruction r))
    (registers : Fin r → E) :
    executeLinear (instruction :: rest) registers =
      executeLinear rest (instruction.execute registers) := rfl

/-- A finite one-call-per-stage program, including its physical answer buffer.
Article: bezout, Algorithms 1--2. Use: actual low-memory executions and history synthesis. -/
structure RegisterProgram (r N : ℕ) where
  initial : Fin r → ℝ
  before : Fin N → List (LinearInstruction r)
  queryRegister : Fin N → Fin r
  answerRegister : Fin N → Fin r
  after : Fin N → List (LinearInstruction r)
  outputRegister : Fin r

/-- Physical vector state together with a scalar oracle-call counter.
The scalar counter introduces no additional vector slot. -/
structure RegisterState (r : ℕ) (E : Type*) where
  vectors : Fin r → E
  calls : ℕ

/-- Physical states agree when their vector slots and scalar call counters agree. -/
@[ext] theorem RegisterState.ext {r : ℕ} {E : Type*} {x y : RegisterState r E}
    (hv : x.vectors = y.vectors) (hc : x.calls = y.calls) : x = y := by
  cases x
  cases y
  simp_all

namespace RegisterProgram
variable {r N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Initial physical registers are scalar multiples of the supplied initial point. -/
def initialState (program : RegisterProgram r N) (initial : E) : RegisterState r E where
  vectors i := program.initial i • initial
  calls := 0

/-- One physical stage: prepare the query, call the oracle once, overwrite the
specified answer buffer, and execute the remaining in-place instructions. -/
def stage (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (s : Fin N) (state : RegisterState r E) : RegisterState r E :=
  let prepared := executeLinear (program.before s) state.vectors
  let answer := oracle s (prepared (program.queryRegister s))
  let answered := Function.update prepared (program.answerRegister s) answer
  ⟨executeLinear (program.after s) answered, state.calls + 1⟩

/-- Exact sequential execution of a prefix of the prescribed calls.
Each recursive state is computed once before its one new physical oracle call. -/
def runPrefix (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) : ℕ → RegisterState r E
  | 0 => program.initialState initial
  | k+1 =>
      let previous := program.runPrefix oracle initial k
      if hk : k < N then program.stage oracle ⟨k,hk⟩ previous else previous

/-- A completed physical program uses exactly the declared finite vector registers. -/
def run (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) : RegisterState r E := program.runPrefix oracle initial N

/-- The physical query seen by the oracle at one declared stage. -/
def queryAt (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) (s : Fin N) : E :=
  (executeLinear (program.before s)
    (program.runPrefix oracle initial s.val).vectors) (program.queryRegister s)

/-- The actual answer returned by that physical oracle call. -/
def answerAt (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) (s : Fin N) : E := oracle s (program.queryAt oracle initial s)

/-- The output is read from the designated physical register after all N calls. -/
def output (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) : E := (program.run oracle initial).vectors program.outputRegister

/-- Every active prefix makes exactly one call per completed stage.
Article: bezout, Algorithms 1--2. Use: exact N-call accounting. -/
theorem runPrefix_calls (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) (k : ℕ) (hk : k ≤ N) :
    (program.runPrefix oracle initial k).calls = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runPrefix, dite_eq_left (by omega)]
    change (program.runPrefix oracle initial k).calls + 1 = k+1
    rw [ih (by omega)]

/-- Exactly N actual oracle calls are made, independently of the oracle's behavior. -/
theorem run_calls (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) : (program.run oracle initial).calls = N :=
  program.runPrefix_calls oracle initial N le_rfl

omit [AddCommGroup E] [Module ℝ E] in
/-- The interpreter carries exactly r vector values throughout every execution. -/
theorem vector_slots (_program : RegisterProgram r N) (_oracle : Fin N → E → E)
    (_initial : E) : Fintype.card (Fin r) = r := Fintype.card_fin r

/-- A constant-answer oracle describes arbitrary physical answer tapes.
Use: the strongest algebraic correspondence, prior to choosing a Hessian or noise law. -/
def tapeOracle (tape : Fin N → E) : Fin N → E → E := fun s _ => tape s

/-- Execution with a prescribed arbitrary answer stream. -/
def runTape (program : RegisterProgram r N) (initial : E) (tape : Fin N → E)
    (k : ℕ) : Fin r → E := (program.runPrefix (tapeOracle tape) initial k).vectors

/-- The in-place program and its own physical answer stream have the same states. -/
theorem runPrefix_eq_tape (program : RegisterProgram r N) (oracle : Fin N → E → E)
    (initial : E) (k : ℕ) :
    (program.runPrefix oracle initial k).vectors =
      program.runTape initial (program.answerAt oracle initial) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [runTape] at ih
    by_cases hk : k < N
    · simp only [runPrefix, dite_eq_left hk, stage, runTape, tapeOracle]
      rw [← ih]
      rfl
    · simp only [runPrefix, dite_eq_right hk, runTape]
      exact ih

end RegisterProgram
end
end bezout.Algorithms
