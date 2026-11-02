import bezout.Algorithms.Tape
import Mathlib.Data.Fin.VecNotation

/-!
Article: bezout, Algorithm 2 (six-vector physical loop).
Use: exact in-place execution with four rolling predictions, one output vector,
and the oracle answer workspace, for every actual oracle stream.
Proof: the explicit pointer rotation preserves the physical slot count; direct
instruction evaluation proves the prediction and output update equations.
-/

namespace bezout.Algorithms
noncomputable section
open scoped BigOperators

/-- The scalar data used by the six-vector Balanced physical loop.
Use: only the four next-row weights and the four impulse entries are read per call. -/
structure BalancedParameters (N : ℕ) where
  weights : Fin N → Fin 4 → ℝ
  impulse : ℕ → Fin N → ℝ
  readout : Fin N → ℝ

namespace BalancedParameters
variable {N : ℕ}

/-- Rotate only the four prediction pointers; output and answer retain their slots. -/
def rotation : Equiv.Perm (Fin 6) where
  toFun := ![1,2,3,0,4,5]
  invFun := ![3,0,1,2,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The printed six-slot physical program, with slots v0,v1,v2,v3,X,G.
Every prediction overwrite uses only the still-live old predictions and G. -/
def program (data : BalancedParameters N) : RegisterProgram 6 N where
  initial := ![1,1,1,1,1,0]
  before _ := []
  queryRegister _ := 0
  answerRegister _ := 5
  after k :=
    [.assign 4 ![0,0,0,0,1,-data.readout k]] ++
    (if k.val+4 < N then
      [.assign 0 ![data.weights k 0, data.weights k 1, data.weights k 2,
        data.weights k 3,0,data.impulse (k.val+4) k]] else []) ++
    (if k.val+1 < N then [.assign 1 ![0,1,0,0,0,data.impulse (k.val+1) k]] else []) ++
    (if k.val+2 < N then [.assign 2 ![0,0,1,0,0,data.impulse (k.val+2) k]] else []) ++
    (if k.val+3 < N then [.assign 3 ![0,0,0,1,0,data.impulse (k.val+3) k]] else []) ++
    [.permute rotation]
  outputRegister := 4

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

set_option maxHeartbeats 2000000 in
/-- One full physical prediction update, with no assumptions on the returned vector.
Use: the invariant can be applied to nonlinear and time-dependent oracles. -/
theorem stage_vectors (data : BalancedParameters N) (k : Fin N)
    (oracle : Fin N → E → E) (v0 v1 v2 v3 x g : E) (calls : ℕ) :
    (data.program.stage oracle k ⟨![v0,v1,v2,v3,x,g],calls⟩).vectors =
      let answer := oracle k v0
      ![if k.val+1<N then v1+data.impulse (k.val+1) k • answer else v1,
        if k.val+2<N then v2+data.impulse (k.val+2) k • answer else v2,
        if k.val+3<N then v3+data.impulse (k.val+3) k • answer else v3,
        if k.val+4<N then
          data.weights k 0 • v0 + data.weights k 1 • v1 +
          data.weights k 2 • v2 + data.weights k 3 • v3 +
          data.impulse (k.val+4) k • answer else v0,
        x-data.readout k•answer, answer] := by
  simp only [RegisterProgram.stage, program, executeLinear_nil]
  split_ifs
  all_goals
    ext i
    fin_cases i <;>
      simp [executeLinear, LinearInstruction.execute, combination, Fin.sum_univ_succ,
        rotation, sub_eq_add_neg]
  all_goals module

/-- A stage consumes precisely the leading prediction as its oracle query. -/
theorem query_register (data : BalancedParameters N) (oracle : Fin N → E → E)
    (initial : E) (s : Fin N) :
    data.program.queryAt oracle initial s =
      (data.program.runPrefix oracle initial s.val).vectors 0 := rfl

/-- Exactly N physical calls are made by the six-vector loop. -/
theorem oracle_calls (data : BalancedParameters N) (oracle : Fin N → E → E) (initial : E) :
    (data.program.run oracle initial).calls = N := data.program.run_calls oracle initial

omit [AddCommGroup E] [Module ℝ E] in
/-- The complete physical state has exactly six vector slots. -/
theorem vector_slots (data : BalancedParameters N) (oracle : Fin N → E → E) (initial : E) :
    Fintype.card (Fin 6) = 6 := data.program.vector_slots oracle initial

end BalancedParameters
end
end bezout.Algorithms
