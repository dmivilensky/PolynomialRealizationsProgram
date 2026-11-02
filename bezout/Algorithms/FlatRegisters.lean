import bezout.Algorithms.PolynomialExecution
import Mathlib.Data.Fin.VecNotation

/-!
Article: bezout, Algorithm 1 (all physical vector assignments).
Use: an exact four-register execution for arbitrary, time-dependent oracles.
Proof: each printed assignment is an in-place instruction; the restoration
identity holds in every real module, independently of the returned answer.
-/

namespace bezout.Algorithms
noncomputable section
open scoped BigOperators

/-- Scalar parameters of the printed Flat iteration. The article's preparation
instantiates these before the physical loop starts. -/
structure FlatParameters (N : ℕ) where
  tau : Fin N → ℝ
  alpha : Fin N → ℝ
  beta : Fin N → ℝ
  terminalA : ℝ
  terminalB : ℝ

namespace FlatParameters
variable {N : ℕ}

/-- Registers are V, P, G, A, in that order. The answer overwrites the temporary
query difference in A; swapping V and P is a pointer renaming. -/
def program (data : FlatParameters N) : RegisterProgram 4 N where
  initial := ![1, 1, 0, 0]
  before s := [.assign 3 ![1,-1,0,0], .assign 0 ![1,0,0,data.tau s]]
  queryRegister _ := 0
  answerRegister _ := 3
  after s :=
    [.assign 0 ![(1 + data.tau s)⁻¹, data.tau s / (1 + data.tau s), 0, 0],
     .assign 2 ![0, 0, data.tau s / (1 + data.tau s), (1 + data.tau s)⁻¹]] ++
    if s.val + 1 < N then
      [.assign 1 ![1 + data.beta s, -data.beta s, -data.alpha s, 0],
       .permute (Equiv.swap 0 1)]
    else [.assign 1 ![1 + data.terminalA, -data.terminalA, -data.terminalB, 0]]
  outputRegister := 1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The in-place query preparation agrees with the displayed extrapolation. -/
theorem before_vectors (data : FlatParameters N) (s : Fin N) (v p g a : E) :
    executeLinear (data.program.before s) ![v,p,g,a] =
      ![v + data.tau s • (v-p), p, g, v-p] := by
  ext i
  fin_cases i <;>
    simp [program, executeLinear, LinearInstruction.execute, combination,
      Fin.sum_univ_succ, sub_eq_add_neg]

/-- Restoration recovers the virtual state even when the oracle returns an
arbitrary vector. Use: no unspoken exact-gradient assumption enters the loop. -/
theorem restoration (t : ℝ) (ht : 1 + t ≠ 0) (v p : E) :
    (1+t)⁻¹ • (v+t•(v-p)) + (t/(1+t)) • p = v := by
  rw [div_eq_mul_inv]
  calc
    _ = (1+t)⁻¹ • ((1+t) • v) := by module
    _ = v := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- The recovered affine-gradient register, including every actual answer. -/
def recoveredGradient (data : FlatParameters N) (s : Fin N) (g answer : E) : E :=
  (1 + data.tau s)⁻¹ • (answer + data.tau s • g)

/-- One complete four-register stage, with the oracle answer kept in A.
Article: Algorithm 1. Use: exact all-oracle-stream operational invariant. -/
theorem stage_vectors (data : FlatParameters N) (s : Fin N)
    (ht : 1 + data.tau s ≠ 0) (oracle : Fin N → E → E)
    (v p g a : E) (calls : ℕ) :
    (data.program.stage oracle s ⟨![v,p,g,a],calls⟩).vectors =
      let answer := oracle s (v + data.tau s • (v-p))
      let nextG := data.recoveredGradient s g answer
      if s.val + 1 < N then
        ![(1+data.beta s)•v-data.beta s•p-data.alpha s•nextG, v, nextG, answer]
      else
        ![v, (1+data.terminalA)•v-data.terminalA•p-data.terminalB•nextG, nextG, answer] := by
  simp only [RegisterProgram.stage, before_vectors]
  split_ifs with hs
  all_goals
    ext i
    fin_cases i <;>
      simp [program, hs, executeLinear, LinearInstruction.execute, combination,
        Fin.sum_univ_succ, Equiv.swap_apply_def, sub_eq_add_neg, recoveredGradient]
  all_goals (match_scalars <;> field_simp [ht] <;> ring)

/-- The affine recovery register equals the current gradient on an exact
linear oracle, provided its preceding value is the preceding virtual gradient. -/
theorem recoveredGradient_linear (data : FlatParameters N) (s : Fin N)
    (ht : 1 + data.tau s ≠ 0) (H : E →ₗ[ℝ] E) (v p : E) :
    data.recoveredGradient s (H p) (H (v + data.tau s • (v-p))) = H v := by
  simp only [recoveredGradient, map_add, map_smul, map_sub]
  match_scalars; field_simp [ht]; ring

/-- The zero-answer run fixes the initial point in both virtual registers.
Use: the induced actual history has normalized queries and terminal. -/
theorem zero_tape (data : FlatParameters N) (ht : ∀ s, 1 + data.tau s ≠ 0)
    (k : ℕ) (hk : k ≤ N) :
    data.program.runTape (1 : ℝ) (fun _ => 0) k = ![1,1,0,0] := by
  induction k with
  | zero => simp [RegisterProgram.runTape, RegisterProgram.runPrefix,
      RegisterProgram.initialState, program]
  | succ k ih =>
    rw [RegisterProgram.runTape_succ _ _ _ k (show k < N by omega), ih (by omega)]
    change (data.program.stage (RegisterProgram.tapeOracle (fun _ => (0:ℝ)))
      ⟨k,by omega⟩ ⟨![1,1,0,0],k⟩).vectors = _
    rw [data.stage_vectors _ (ht _)]
    simp only [RegisterProgram.tapeOracle, smul_zero, add_zero,
      recoveredGradient]
    split_ifs <;> ext i <;> fin_cases i <;> simp [smul_eq_mul]

/-- Every actual query and the actual terminal have initial-point coefficient one. -/
theorem normalized (data : FlatParameters N) (ht : ∀ s, 1 + data.tau s ≠ 0) :
    data.program.TranslationNormalized where
  query s := by
    rw [RegisterProgram.queryCoefficient_initial_value, data.zero_tape ht s.val (Nat.le_of_lt s.isLt)]
    rw [data.before_vectors]
    simp [program]
  output := by
    unfold RegisterProgram.outputCoefficient
    rw [RegisterProgram.coefficientState_initial_value, data.zero_tape ht N le_rfl]
    rfl

omit [AddCommGroup E] [Module ℝ E] in
/-- Four physical vectors suffice throughout every oracle execution. -/
theorem vector_slots (data : FlatParameters N) (oracle : Fin N → E → E) (initial : E) :
    Fintype.card (Fin 4) = 4 := data.program.vector_slots oracle initial

/-- The four-slot implementation makes exactly N physical oracle calls. -/
theorem oracle_calls (data : FlatParameters N) (oracle : Fin N → E → E) (initial : E) :
    (data.program.run oracle initial).calls = N := data.program.run_calls oracle initial

end FlatParameters
end
end bezout.Algorithms
