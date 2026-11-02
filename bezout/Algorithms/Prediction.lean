import bezout.Algorithms.BalancedRegisters

/-!
Article: bezout, Algorithm 2 and Appendix C's prediction invariant.
Use: four rolling predictions implement a causal history for every answer tape.
Proof: an affine fourth-order row relation propagates the zero-future-answer
predictions, and the new answer adds its exact causal impulse to each live slot.
-/

namespace bezout.Algorithms
noncomputable section
open scoped BigOperators

/-- A finite causal prefix sum includes exactly the prescribed physical answers. -/
theorem sum_prefix_succ {N : ℕ} {E : Type*} [AddCommMonoid E]
    (f : Fin N → E) (k : ℕ) (hk : k < N) :
    (∑ i : Fin N, if i.val < k+1 then f i else 0) =
      (∑ i : Fin N, if i.val < k then f i else 0) + f ⟨k,hk⟩ := by
  have he (i : Fin N) : (if i.val < k+1 then f i else 0) =
      (if i.val < k then f i else 0) + (if i=⟨k,hk⟩ then f i else 0) := by
    by_cases hi : i.val < k
    · have hne : i ≠ ⟨k,hk⟩ := by intro he; have hv : i.val = k := congrArg Fin.val he; omega
      simp [hi, show i.val < k+1 by omega, hne]
    · by_cases he : i=⟨k,hk⟩
      · subst i; simp
      · have hi' : ¬i.val<k+1 := by
          intro hh
          exact he (Fin.ext (show i.val=k by omega))
        simp [hi,hi',he]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

end
end bezout.Algorithms

namespace bezout.History
noncomputable section
open scoped BigOperators
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A future query predicted using only the first k already returned answers. -/
def prediction (h : bezout.History N) (initial : E) (tape : Fin N → E)
    (j : Fin N) (k : ℕ) : E :=
  initial - ∑ i : Fin N, if i.val < k then h.a j i • tape i else 0

/-- One new answer changes each future prediction by exactly its causal impulse. -/
theorem prediction_succ (h : bezout.History N) (initial : E) (tape : Fin N → E)
    (j : Fin N) (k : ℕ) (hk : k < N) :
    h.prediction initial tape j (k+1) =
      h.prediction initial tape j k - h.a j ⟨k,hk⟩ • tape ⟨k,hk⟩ := by
  unfold prediction
  rw [bezout.Algorithms.sum_prefix_succ _ k hk]
  abel

/-- At its physical stage a causal prediction is the complete history query. -/
theorem prediction_current (h : bezout.History N) (initial : E) (tape : Fin N → E)
    (j : Fin N) :
    h.prediction initial tape j j.val = initial - ∑ i : Fin N, h.a j i • tape i := by
  unfold prediction
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < j.val
  · simp [hi]
  · simp [hi, h.triangular j i (show j ≤ i by omega)]

end
end bezout.History

namespace bezout.Algorithms
noncomputable section
open scoped BigOperators
namespace BalancedParameters
variable {N : ℕ}

/-- The printed local scalar table is compatible with an actual causal history.
Only old-answer coefficients enter the fourth prediction; the four new impulses
are supplied separately by the physical algorithm. -/
structure Compatible (data : BalancedParameters N) (h : bezout.History N) : Prop where
  impulse : ∀ (k : Fin N) (j : ℕ) (hj : j < N), data.impulse j k = -h.a ⟨j,hj⟩ k
  readout : data.readout = h.b
  affine : ∀ (k : Fin N) (_ : k.val+4<N), ∑ r : Fin 4, data.weights k r = 1
  past : ∀ (k : Fin N) (hk : k.val+4<N) (i : Fin N) (_ : i.val<k.val),
    h.a ⟨k.val+4,hk⟩ i = ∑ r : Fin 4,
      data.weights k r * h.a ⟨k.val+r.val,by omega⟩ i

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The six-slot update specialized to an arbitrary prescribed answer tape. -/
theorem tape_step (data : BalancedParameters N) (initial : E) (tape : Fin N → E)
    (k : Fin N) :
    data.program.runTape initial tape (k.val+1) =
      let v := data.program.runTape initial tape k.val
      ![if k.val+1<N then v 1+data.impulse (k.val+1) k • tape k else v 1,
        if k.val+2<N then v 2+data.impulse (k.val+2) k • tape k else v 2,
        if k.val+3<N then v 3+data.impulse (k.val+3) k • tape k else v 3,
        if k.val+4<N then
          data.weights k 0 • v 0 + data.weights k 1 • v 1 +
          data.weights k 2 • v 2 + data.weights k 3 • v 3 +
          data.impulse (k.val+4) k • tape k else v 0,
        v 4-data.readout k•tape k, tape k] := by
  let v := data.program.runTape initial tape k.val
  have hv : ![v 0,v 1,v 2,v 3,v 4,v 5] = v := by ext i; fin_cases i <;> rfl
  have hs := data.stage_vectors k (RegisterProgram.tapeOracle tape)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) 0
  rw [hv] at hs
  rw [RegisterProgram.runTape_succ _ _ _ k.val k.isLt]
  simpa only [RegisterProgram.stage, RegisterProgram.tapeOracle, v] using hs

/-- The rolling registers predict exactly the future history queries with all
not-yet-returned answers set to zero; X accumulates the exact history readout. -/
structure PredictionInvariant (data : BalancedParameters N) (h : bezout.History N)
    (initial : E) (tape : Fin N → E) (k : ℕ) : Prop where
  predictions : ∀ (r : Fin 4) (hr : k+r.val<N),
    data.program.runTape initial tape k ⟨r.val,by omega⟩ =
      h.prediction initial tape ⟨k+r.val,hr⟩ k
  output : data.program.runTape initial tape k 4 =
    initial - ∑ i : Fin N, if i.val<k then h.b i • tape i else 0

/-- The weighted four old predictions equal the next zero-future-answer prediction. -/
theorem prediction_recurrence (data : BalancedParameters N) (h : bezout.History N)
    (hc : data.Compatible h) (initial : E) (tape : Fin N → E)
    (k : Fin N) (hk : k.val+4<N) :
    (∑ r : Fin 4, data.weights k r •
      h.prediction initial tape ⟨k.val+r.val,by omega⟩ k.val) =
      h.prediction initial tape ⟨k.val+4,hk⟩ k.val := by
  simp only [bezout.History.prediction, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, hc.affine k hk, one_smul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k.val
  · simp only [hi, ite_true, smul_smul]
    rw [← Finset.sum_smul, hc.past k hk i hi]
  · simp [hi]

/-- The four prediction and output invariants hold after every actual answer tape prefix. -/
theorem prediction_invariant (data : BalancedParameters N) (h : bezout.History N)
    (hc : data.Compatible h) (initial : E) (tape : Fin N → E)
    (k : ℕ) (hk : k ≤ N) : data.PredictionInvariant h initial tape k := by
  induction k with
  | zero =>
    constructor
    · intro r hr
      unfold RegisterProgram.runTape RegisterProgram.runPrefix RegisterProgram.initialState
      fin_cases r <;>
        simp [program, bezout.History.prediction]
    · simp [RegisterProgram.runTape, RegisterProgram.runPrefix, RegisterProgram.initialState, program]
  | succ k ih =>
    have hkN : k < N := by omega
    have old := ih (by omega)
    have step := data.tape_step initial tape ⟨k,hkN⟩
    constructor
    · intro r hr
      fin_cases r
      · rw [step]
        change (if k+1<N then data.program.runTape initial tape k 1 +
          data.impulse (k+1) ⟨k,hkN⟩ • tape ⟨k,hkN⟩ else _) =
          h.prediction initial tape ⟨k+1,by omega⟩ (k+1)
        have ho : data.program.runTape initial tape k 1 =
            h.prediction initial tape ⟨k+1,by omega⟩ k := old.predictions 1 (by omega)
        rw [ite_eq_left (by omega), ho, hc.impulse _ _ (by omega)]
        rw [h.prediction_succ initial tape _ k hkN]
        simp only [neg_smul, sub_eq_add_neg]
      · rw [step]
        change (if k+2<N then data.program.runTape initial tape k 2 +
          data.impulse (k+2) ⟨k,hkN⟩ • tape ⟨k,hkN⟩ else _) =
          h.prediction initial tape ⟨k+2,by omega⟩ (k+1)
        have ho : data.program.runTape initial tape k 2 =
            h.prediction initial tape ⟨k+2,by omega⟩ k := old.predictions 2 (by omega)
        rw [ite_eq_left (by omega), ho, hc.impulse _ _ (by omega)]
        rw [h.prediction_succ initial tape _ k hkN]
        simp only [neg_smul, sub_eq_add_neg]
      · rw [step]
        change (if k+3<N then data.program.runTape initial tape k 3 +
          data.impulse (k+3) ⟨k,hkN⟩ • tape ⟨k,hkN⟩ else _) =
          h.prediction initial tape ⟨k+3,by omega⟩ (k+1)
        have ho : data.program.runTape initial tape k 3 =
            h.prediction initial tape ⟨k+3,by omega⟩ k := old.predictions 3 (by omega)
        rw [ite_eq_left (by omega), ho, hc.impulse _ _ (by omega)]
        rw [h.prediction_succ initial tape _ k hkN]
        simp only [neg_smul, sub_eq_add_neg]
      · change k+4<N at hr
        rw [step]
        change (if k+4<N then
          data.weights ⟨k,hkN⟩ 0 • data.program.runTape initial tape k 0 +
          data.weights ⟨k,hkN⟩ 1 • data.program.runTape initial tape k 1 +
          data.weights ⟨k,hkN⟩ 2 • data.program.runTape initial tape k 2 +
          data.weights ⟨k,hkN⟩ 3 • data.program.runTape initial tape k 3 +
          data.impulse (k+4) ⟨k,hkN⟩ • tape ⟨k,hkN⟩ else _) =
          h.prediction initial tape ⟨k+4,by omega⟩ (k+1)
        have h0 : data.program.runTape initial tape k 0 =
            h.prediction initial tape ⟨k,by omega⟩ k := old.predictions 0 (by omega)
        have h1 : data.program.runTape initial tape k 1 =
            h.prediction initial tape ⟨k+1,by omega⟩ k := old.predictions 1 (by omega)
        have h2 : data.program.runTape initial tape k 2 =
            h.prediction initial tape ⟨k+2,by omega⟩ k := old.predictions 2 (by omega)
        have h3 : data.program.runTape initial tape k 3 =
            h.prediction initial tape ⟨k+3,by omega⟩ k := old.predictions 3 (by omega)
        rw [ite_eq_left (by omega), h0, h1, h2, h3, hc.impulse _ _ (by omega)]
        have hp := data.prediction_recurrence h hc initial tape ⟨k,hkN⟩ (by omega)
        simp [Fin.sum_univ_succ, ← add_assoc] at hp
        rw [hp]
        rw [h.prediction_succ initial tape _ k hkN]
        simp only [neg_smul, sub_eq_add_neg]
    · rw [step]
      simp only [Matrix.cons_val]
      rw [old.output, hc.readout, sum_prefix_succ _ k hkN]
      abel

/-- Every physical query on every answer tape is the actual history query. -/
theorem tape_query_history (data : BalancedParameters N) (h : bezout.History N)
    (hc : data.Compatible h) (initial : E) (tape : Fin N → E) (s : Fin N) :
    executeLinear (data.program.before s) (data.program.runTape initial tape s.val)
      (data.program.queryRegister s) = initial - ∑ i : Fin N, h.a s i • tape i := by
  have hi := data.prediction_invariant h hc initial tape s.val (Nat.le_of_lt s.isLt)
  have hp : data.program.runTape initial tape s.val 0 = h.prediction initial tape s s.val :=
    hi.predictions 0 (by exact s.isLt)
  change data.program.runTape initial tape s.val 0 = _
  rw [hp, h.prediction_current]

/-- The physical output register equals the actual history readout on every answer tape. -/
theorem tape_output_history (data : BalancedParameters N) (h : bezout.History N)
    (hc : data.Compatible h) (initial : E) (tape : Fin N → E) :
    data.program.runTape initial tape N data.program.outputRegister =
      initial - ∑ i : Fin N, h.b i • tape i := by
  have hi := (data.prediction_invariant h hc initial tape N le_rfl).output
  simpa only [program, Fin.is_lt, ite_true] using hi

/-- The actual oracle answers in the six-slot loop are the canonical history answers. -/
theorem answers_eq_history (data : BalancedParameters N) (h : bezout.History N)
    (hc : data.Compatible h) (oracle : Fin N → E → E) (initial : E) :
    data.program.answerAt oracle initial = h.oracleAnswers initial oracle := by
  apply h.oracleAnswers_unique
  intro s
  unfold RegisterProgram.answerAt RegisterProgram.queryAt
  rw [RegisterProgram.runPrefix_eq_tape, data.tape_query_history h hc]
  rfl

/-- The complete physical query stream equals the history stream for arbitrary oracles. -/
theorem query_eq_history (data : BalancedParameters N) (h : bezout.History N)
    (hc : data.Compatible h) (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    data.program.queryAt oracle initial s = h.oracleQuery initial oracle s := by
  unfold RegisterProgram.queryAt bezout.History.oracleQuery
  rw [RegisterProgram.runPrefix_eq_tape, data.tape_query_history h hc,
    data.answers_eq_history h hc]

/-- The physical six-slot output equals the actual history for every oracle stream. -/
theorem output_eq_history (data : BalancedParameters N) (h : bezout.History N)
    (hc : data.Compatible h) (oracle : Fin N → E → E) (initial : E) :
    data.program.output oracle initial = h.oracleOutput initial oracle := by
  unfold RegisterProgram.output RegisterProgram.run bezout.History.oracleOutput
  rw [RegisterProgram.runPrefix_eq_tape, data.tape_output_history h hc,
    data.answers_eq_history h hc]

end BalancedParameters
end
end bezout.Algorithms
