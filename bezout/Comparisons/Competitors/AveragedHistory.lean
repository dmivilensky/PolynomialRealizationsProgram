import bezout.Comparisons.Competitors.Averaging

/-!
Article: bezout, Equation `eq:competitor-dfb` and the general physical response.
Use: the literal running-average implementation is itself an unrestricted causal
history for every vector space and every time-dependent oracle. Thus all matrix
and covariance theorems apply to its actual physical errors.
Proof: average the exact affine answer coefficients of the cached physical
iterates; their initial coefficients are all one and their queries are unchanged.
-/

namespace bezout.Comparisons.Competitors.Momentum
noncomputable section
open scoped BigOperators
open bezout.Algorithms Polynomial

/-- Exact physical answer weights of the running average. -/
def averagedWeight (data : Momentum) (N : ℕ) (s : Fin N) : ℝ :=
  -(((N:ℝ)+1)⁻¹*∑ j ∈ Finset.range (N+1), (data.program N).coefficientState j 0 (some s))

/-- The causal history of the literal running-average output, with unchanged queries. -/
def averagedHistory (data : Momentum) (N : ℕ) : bezout.History N where
  a := (data.history N).a
  b := data.averagedWeight N
  triangular := (data.history N).triangular

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The running average uses exactly the same physical oracle-answer stream. -/
theorem averaged_answers (data : Momentum) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    (data.averagedHistory N).oracleAnswers initial oracle=(data.history N).oracleAnswers initial oracle := by
  symm
  apply bezout.History.oracleAnswers_unique
  intro s
  exact (data.history N).oracleAnswers_eq initial oracle s

/-- Every physical iterate has initial coefficient one in its exact affine tape expansion. -/
theorem prefix_tape_expansion (data : Momentum) (N : ℕ) (initial : E)
    (tape : Fin N → E) (j : ℕ) (hj : j≤N) :
    (data.program N).runTape initial tape j 0=initial+
      ∑ s, (data.program N).coefficientState j 0 (some s) • tape s := by
  have h := congrFun ((data.program N).runTape_expansion initial tape j) 0
  have hc : (data.program N).coefficientState j 0 none=1 := by
    rw [RegisterProgram.coefficientState_initial_value,data.zero_tape N j hj]
    rfl
  simpa only [RegisterProgram.evaluateSymbols_apply,Fintype.sum_option,hc,one_smul] using h

/-- Exact affine average of one cached physical trajectory, for an arbitrary oracle. -/
theorem averagedOutput_expansion (data : Momentum) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    data.averagedOutput N oracle initial=initial-
      ∑ s, data.averagedWeight N s • (data.program N).answerAt oracle initial s := by
  rw [data.averagedOutput_eq]
  have hp (j : ℕ) (hj : j∈Finset.range (N+1)) :
      ((data.program N).runPrefix oracle initial j).vectors 0=initial+
        ∑ s, (data.program N).coefficientState j 0 (some s) • (data.program N).answerAt oracle initial s := by
    rw [RegisterProgram.runPrefix_eq_tape]
    exact data.prefix_tape_expansion N initial _ j (by have := Finset.mem_range.mp hj; omega)
  rw [Finset.sum_congr rfl hp,Finset.sum_add_distrib,smul_add,Finset.sum_const,Finset.card_range,
    ← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  have hc : ((N:ℝ)+1)⁻¹*(N+1:ℕ)=1 := by
    rw [Nat.cast_add,Nat.cast_one,inv_mul_cancel₀ (by positivity : (N:ℝ)+1≠0)]
  rw [hc,one_smul,Finset.sum_comm,Finset.smul_sum]
  simp only [averagedWeight,neg_smul,Finset.sum_neg_distrib,sub_neg_eq_add,
    ]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_smul,smul_smul]

/-- Complete all-oracle-stream equivalence between averaging and its causal history. -/
theorem averagedOutput_eq_history (data : Momentum) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    data.averagedOutput N oracle initial=(data.averagedHistory N).oracleOutput initial oracle := by
  rw [data.averagedOutput_expansion]
  unfold bezout.History.oracleOutput
  rw [data.averaged_answers,RegisterProgram.answers_eq_history]
  rfl

/-- Exact vector and matrix physical-response decomposition of the averaged execution. -/
theorem averaged_physical_response (data : Momentum) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) :
    data.averagedOutput N (fun s y => H y+noise s) initial=
      (aeval H (data.averagedHistory N).terminal) initial+
        ∑ s, (aeval H ((data.averagedHistory N).response s)) (noise s) := by
  rw [data.averagedOutput_eq_history,bezout.History.oracleOutput_linear]
  exact bezout.History.physical_response _ H initial noise _

end
end bezout.Comparisons.Competitors.Momentum
