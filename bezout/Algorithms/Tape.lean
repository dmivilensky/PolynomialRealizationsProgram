import bezout.Algorithms.Registers
import bezout.History.Oracle

/-!
Article: bezout, Algorithms 1--2 and Theorem 2.1.
Use: a genuine finite-register execution determines a causal coefficient
history, and the two implementations agree for every time-dependent oracle.
Proof: execute the in-place instructions on the formal basis consisting of
one initial-value coordinate and one coordinate for each physical answer.
-/

namespace bezout.Algorithms

open scoped BigOperators
noncomputable section

variable {r N : ℕ} {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Linear maps commute with the register linear combination. -/
theorem combination_map (T : E →ₗ[ℝ] F) (w : Fin r → ℝ) (u : Fin r → E) :
    T (combination w u) = combination w (fun i => T (u i)) := by
  simp [combination]

/-- Every in-place linear instruction commutes with a linear physical map. -/
theorem LinearInstruction.execute_map (T : E →ₗ[ℝ] F)
    (instruction : LinearInstruction r) (u : Fin r → E) :
    (fun i => T (instruction.execute u i)) =
      instruction.execute (fun i => T (u i)) := by
  cases instruction with
  | assign target weights =>
    funext i
    by_cases hi : i = target
    · subst i
      simp [LinearInstruction.execute, combination_map]
    · simp [LinearInstruction.execute, hi]
  | permute order => rfl

/-- A sequence of physical assignments commutes with every linear physical map. -/
theorem executeLinear_map (T : E →ₗ[ℝ] F) (instructions : List (LinearInstruction r))
    (u : Fin r → E) :
    (fun i => T (executeLinear instructions u i)) =
      executeLinear instructions (fun i => T (u i)) := by
  induction instructions generalizing u with
  | nil => rfl
  | cons instruction rest ih =>
    rw [executeLinear_cons, executeLinear_cons, ← instruction.execute_map T]
    exact ih _

/-- Linear assignments preserve an entirely zero physical register state. -/
theorem executeLinear_zero (instructions : List (LinearInstruction r)) :
    executeLinear instructions (fun _ => (0 : E)) = fun _ => 0 := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    rw [executeLinear_cons]
    have hz : instruction.execute (fun _ => (0 : E)) = fun _ => 0 := by
      cases instruction <;> simp [LinearInstruction.execute, combination]
    rw [hz, ih]

namespace RegisterProgram

/-- Prescribed-answer execution advances by precisely the printed linear instructions. -/
theorem runTape_succ (program : RegisterProgram r N) (initial : E) (tape : Fin N → E)
    (k : ℕ) (hk : k < N) :
    program.runTape initial tape (k+1) =
      executeLinear (program.after ⟨k,hk⟩)
        (Function.update (executeLinear (program.before ⟨k,hk⟩)
          (program.runTape initial tape k)) (program.answerRegister ⟨k,hk⟩) (tape ⟨k,hk⟩)) := by
  simp only [runTape, runPrefix, dite_eq_left hk, stage, tapeOracle]

/-- A prescribed-answer execution commutes with a linear physical map. -/
theorem runTape_map (program : RegisterProgram r N) (T : E →ₗ[ℝ] F)
    (initial : E) (tape : Fin N → E) (k : ℕ) :
    (fun i => T (program.runTape initial tape k i)) =
      program.runTape (T initial) (fun s => T (tape s)) k := by
  induction k with
  | zero => simp [runTape, runPrefix, initialState]
  | succ k ih =>
    by_cases hk : k < N
    · rw [program.runTape_succ initial tape k hk,
        program.runTape_succ (T initial) (fun s => T (tape s)) k hk, executeLinear_map]
      have hu : (fun i => T ((Function.update
          (executeLinear (program.before ⟨k,hk⟩) (program.runTape initial tape k))
          (program.answerRegister ⟨k,hk⟩) (tape ⟨k,hk⟩)) i)) =
          Function.update
            (executeLinear (program.before ⟨k,hk⟩)
              (program.runTape (T initial) (fun s => T (tape s)) k))
            (program.answerRegister ⟨k,hk⟩) (T (tape ⟨k,hk⟩)) := by
        rw [← ih, ← executeLinear_map]
        funext i
        by_cases hi : i = program.answerRegister ⟨k,hk⟩ <;> simp [hi]
      rw [hu]
    · simpa only [runTape, runPrefix, dite_eq_right hk] using ih

/-- The formal initial-value basis coordinate. -/
def initialSymbol : Option (Fin N) → ℝ := Pi.single none 1

/-- The formal basis coordinate of a physical oracle answer. -/
def answerSymbol (s : Fin N) : Option (Fin N) → ℝ := Pi.single (some s) 1

/-- Exact coefficients of every register after a prefix of arbitrary answers. -/
def coefficientState (program : RegisterProgram r N) (k : ℕ) :
    Fin r → Option (Fin N) → ℝ :=
  program.runTape initialSymbol answerSymbol k

/-- Exact affine coefficients of the actual physical query at stage s. -/
def queryCoefficient (program : RegisterProgram r N) (s : Fin N) : Option (Fin N) → ℝ :=
  (executeLinear (program.before s) (program.coefficientState s.val))
    (program.queryRegister s)

/-- Exact affine coefficients of the final physical output. -/
def outputCoefficient (program : RegisterProgram r N) : Option (Fin N) → ℝ :=
  program.coefficientState N program.outputRegister

/-- Evaluate the formal initial/answer basis in any real vector space. -/
def evaluateSymbols (values : Option (Fin N) → E) :
    (Option (Fin N) → ℝ) →ₗ[ℝ] E where
  toFun c := ∑ j, c j • values j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- Evaluation of the symbolic affine coefficients is the finite physical sum. -/
@[simp] theorem evaluateSymbols_apply (values : Option (Fin N) → E)
    (c : Option (Fin N) → ℝ) : evaluateSymbols values c = ∑ j, c j • values j := rfl

/-- Each formal basis vector evaluates to its prescribed physical value. -/
@[simp] theorem evaluateSymbols_single (values : Option (Fin N) → E)
    (j : Option (Fin N)) : evaluateSymbols values (Pi.single j 1) = values j := by
  classical
  cases j <;> simp [evaluateSymbols_apply, Pi.single_apply]

/-- Every physical register is exactly its symbolic affine answer expansion. -/
theorem runTape_expansion (program : RegisterProgram r N) (initial : E)
    (tape : Fin N → E) (k : ℕ) :
    program.runTape initial tape k = fun i =>
      evaluateSymbols (fun j => match j with | none => initial | some s => tape s)
        (program.coefficientState k i) := by
  let values : Option (Fin N) → E := fun j => match j with | none => initial | some s => tape s
  have hm := program.runTape_map (evaluateSymbols values) initialSymbol answerSymbol k
  have hi : evaluateSymbols values initialSymbol = initial := by simp [initialSymbol, values]
  have ha : (fun s : Fin N => evaluateSymbols values (answerSymbol s)) = tape := by
    funext s
    simp [answerSymbol, values]
  rw [hi, ha] at hm
  exact hm.symm

/-- The exact symbolic affine expansion of a physical query on an arbitrary answer tape. -/
theorem tape_query_expansion (program : RegisterProgram r N) (initial : E)
    (tape : Fin N → E) (s : Fin N) :
    (executeLinear (program.before s) (program.runTape initial tape s.val))
      (program.queryRegister s) =
      evaluateSymbols (fun j => match j with | none => initial | some k => tape k)
        (program.queryCoefficient s) := by
  rw [program.runTape_expansion, ← executeLinear_map]
  rfl

/-- The exact symbolic affine expansion of the output on an arbitrary answer tape. -/
theorem tape_output_expansion (program : RegisterProgram r N) (initial : E)
    (tape : Fin N → E) :
    program.runTape initial tape N program.outputRegister =
      evaluateSymbols (fun j => match j with | none => initial | some k => tape k)
        program.outputCoefficient := by
  rw [program.runTape_expansion]
  rfl

/-- A fixed formal coordinate that vanishes in all registers is preserved by every instruction. -/
theorem executeLinear_coordinate_zero (instructions : List (LinearInstruction r))
    (u : Fin r → Option (Fin N) → ℝ) (j : Option (Fin N))
    (hu : ∀ i, u i j = 0) : ∀ i, executeLinear instructions u i j = 0 := by
  let T : (Option (Fin N) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  have hm := executeLinear_map T instructions u
  have hz : (fun i => T (u i)) = fun _ => (0 : ℝ) := funext hu
  rw [hz, executeLinear_zero] at hm
  intro i
  exact congrFun hm i

/-- Coefficients of answers not yet observed are identically zero in every physical register. -/
theorem coefficientState_future_zero (program : RegisterProgram r N) (k : ℕ) (hk : k ≤ N)
    (j : Fin N) (hkj : k ≤ j.val) : ∀ i, program.coefficientState k i (some j) = 0 := by
  induction k with
  | zero => simp [coefficientState, runTape, runPrefix, initialState, initialSymbol]
  | succ k ih =>
    have hkN : k < N := by omega
    unfold coefficientState
    rw [program.runTape_succ initialSymbol answerSymbol k hkN]
    apply executeLinear_coordinate_zero
    intro i
    by_cases hi : i = program.answerRegister ⟨k,hkN⟩
    · subst i
      have hne : j ≠ (⟨k,hkN⟩ : Fin N) := by
        intro he
        have hv : j.val = k := congrArg Fin.val he
        omega
      simp [answerSymbol, hne]
    · rw [Function.update_of_ne hi]
      exact executeLinear_coordinate_zero _ _ _ (ih (by omega) (by omega)) i

/-- A physical query contains no current or future oracle answer coefficient. -/
theorem queryCoefficient_future_zero (program : RegisterProgram r N)
    (s j : Fin N) (hsj : s ≤ j) : program.queryCoefficient s (some j) = 0 := by
  apply executeLinear_coordinate_zero
  exact program.coefficientState_future_zero s.val (by omega) j hsj

/-- Formal initial-value coefficients equal the actual zero-answer execution.
Use: translation normalization is checked by the same in-place program. -/
theorem coefficientState_initial_value (program : RegisterProgram r N) (k : ℕ) (i : Fin r) :
    program.coefficientState k i none = program.runTape (1 : ℝ) (fun _ => 0) k i := by
  have he := congrFun (program.runTape_expansion (1 : ℝ) (fun _ => 0) k) i
  simpa only [evaluateSymbols_apply, Fintype.sum_option, smul_eq_mul, mul_one,
    mul_zero, Finset.sum_const_zero, add_zero] using he.symm

/-- Query normalization can be verified on the actual zero-answer execution. -/
theorem queryCoefficient_initial_value (program : RegisterProgram r N) (s : Fin N) :
    program.queryCoefficient s none =
      executeLinear (program.before s) (program.runTape (1 : ℝ) (fun _ => 0) s.val)
        (program.queryRegister s) := by
  have he := program.tape_query_expansion (1 : ℝ) (fun _ => 0) s
  simpa only [evaluateSymbols_apply, Fintype.sum_option, smul_eq_mul, mul_one,
    mul_zero, Finset.sum_const_zero, add_zero] using he.symm

/-- Translation normalization is an explicit scalar statement about actual program coefficients. -/
structure TranslationNormalized (program : RegisterProgram r N) : Prop where
  query : ∀ s, program.queryCoefficient s none = 1
  output : program.outputCoefficient none = 1

/-- The actual causal history induced by a normalized finite-register program. -/
def history (program : RegisterProgram r N) (_hn : program.TranslationNormalized) : bezout.History N where
  a s j := - program.queryCoefficient s (some j)
  b j := - program.outputCoefficient (some j)
  triangular s j hsj := by rw [program.queryCoefficient_future_zero s j hsj, neg_zero]

/-- Every physical query equals the induced history query for every arbitrary answer stream. -/
theorem tape_query_history (program : RegisterProgram r N) (hn : program.TranslationNormalized)
    (initial : E) (tape : Fin N → E) (s : Fin N) :
    (executeLinear (program.before s) (program.runTape initial tape s.val))
      (program.queryRegister s) = initial - ∑ j, (program.history hn).a s j • tape j := by
  rw [program.tape_query_expansion]
  simp only [evaluateSymbols_apply, Fintype.sum_option, hn.query, one_smul, history, neg_smul]
  rw [Finset.sum_neg_distrib]
  abel

/-- The physical output equals the induced history output on every answer stream. -/
theorem tape_output_history (program : RegisterProgram r N) (hn : program.TranslationNormalized)
    (initial : E) (tape : Fin N → E) :
    program.runTape initial tape N program.outputRegister =
      initial - ∑ j, (program.history hn).b j • tape j := by
  rw [program.tape_output_expansion]
  simp only [evaluateSymbols_apply, Fintype.sum_option, hn.output, one_smul, history, neg_smul]
  rw [Finset.sum_neg_distrib]
  abel

/-- The actual program answer stream is exactly the canonical causal history answer stream. -/
theorem answers_eq_history (program : RegisterProgram r N) (hn : program.TranslationNormalized)
    (initial : E) (oracle : Fin N → E → E) :
    program.answerAt oracle initial = (program.history hn).oracleAnswers initial oracle := by
  apply bezout.History.oracleAnswers_unique
  intro s
  unfold answerAt queryAt
  rw [program.runPrefix_eq_tape]
  rw [program.tape_query_history hn]
  rfl

/-- Every actual oracle query agrees between the in-place program and its causal history. -/
theorem query_eq_history (program : RegisterProgram r N) (hn : program.TranslationNormalized)
    (initial : E) (oracle : Fin N → E → E) (s : Fin N) :
    program.queryAt oracle initial s = (program.history hn).oracleQuery initial oracle s := by
  unfold queryAt bezout.History.oracleQuery
  rw [program.runPrefix_eq_tape, program.tape_query_history hn, program.answers_eq_history hn]

/-- All-oracle-stream equivalence of a physical finite-register program and its actual history. -/
theorem output_eq_history (program : RegisterProgram r N) (hn : program.TranslationNormalized)
    (initial : E) (oracle : Fin N → E → E) :
    program.output oracle initial = (program.history hn).oracleOutput initial oracle := by
  unfold output run
  rw [program.runPrefix_eq_tape, program.tape_output_history hn, program.answers_eq_history hn]
  rfl

end RegisterProgram
end
end bezout.Algorithms
