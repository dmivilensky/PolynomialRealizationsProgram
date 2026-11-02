import bezout.Algorithms.FlatRegisters
import bezout.Algorithms.FlatPreparation

/-!
Article: bezout, Algorithm 1 and its Appendix B verification.
Use: the literal four-vector program realizes the actual Flat history for every
oracle stream, including arbitrary additive errors at every physical call.
Proof: symbolic nominal virtual states obey the normalized U recurrence; the
unique causal history theorem identifies the full answer-tape coefficients.
-/

namespace bezout.Algorithms.Flat
noncomputable section
open Polynomial
open scoped BigOperators

/-- All prepared scalar data of the printed Flat algorithm. -/
def parameters (I : chebyshev1.SpectralInterval) (N : ℕ) : FlatParameters N where
  tau s := bezout.Flat.tau I N s
  alpha s := bezout.Flat.alpha I s
  beta s := bezout.Flat.beta I s
  terminalA := bezout.Flat.terminalA I N
  terminalB := bezout.Flat.terminalB I N

/-- Algorithm 1 as four actual in-place registers V, P, G, A. -/
def program (I : chebyshev1.SpectralInterval) (N : ℕ) : RegisterProgram 4 N :=
  (parameters I N).program

/-- The same scalar table computed solely by the printed scalar recurrences. -/
def preparedParameters (I : chebyshev1.SpectralInterval) (N : ℕ) : FlatParameters N where
  tau s := preparedTau I N s.val
  alpha s := if s.val=0 then 2/(I.L+I.mu) else
    4*preparedU I s.val/(I.delta*preparedU I (s.val+1))
  beta s := if s.val=0 then 0 else preparedU I (s.val-1)/preparedU I (s.val+1)
  terminalA := preparedU I (N-2)/preparedDen I N
  terminalB := 2*preparedU I (N-1)/(I.delta*preparedDen I N)

/-- Every scalar entry of the recursive preparation is the exact physical table. -/
theorem preparedParameters_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    preparedParameters I N = parameters I N := by
  simp only [preparedParameters, parameters, preparedU_eq, preparedDen_eq I N hN,
    bezout.Flat.alpha, bezout.Flat.beta, bezout.Flat.terminalA, bezout.Flat.terminalB]
  congr 1
  funext s
  exact preparedTau_eq I N hN s

/-- Algorithm 1 with every scalar supplied by the actual recursive preparation. -/
def preparedProgram (I : chebyshev1.SpectralInterval) (N : ℕ) : RegisterProgram 4 N :=
  (preparedParameters I N).program

/-- Recursive scalar preparation produces precisely the proved four-vector program. -/
theorem preparedProgram_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    preparedProgram I N = program I N := by rw [preparedProgram, preparedParameters_eq I N hN]; rfl

/-- Every recovery denominator is strictly positive. -/
theorem denominator_pos (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : 0 < 1 + (parameters I N).tau s := by
  have ht := bezout.Flat.tau_nonneg I N (by omega) s.val s.isLt
  change 0 < 1 + bezout.Flat.tau I N s
  linarith

/-- The actual physical program is translation normalized. -/
theorem normalized (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (program I N).TranslationNormalized :=
  (parameters I N).normalized (fun s => ne_of_gt (denominator_pos I N hN s))

/-- The affine extrapolated physical query polynomial. -/
def physicalQuery (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  bezout.Flat.virtualPolynomial I s + C (bezout.Flat.tau I N s) *
    (bezout.Flat.virtualPolynomial I s - bezout.Flat.virtualPolynomial I (s-1))

/-- The symbolic oracle is multiplication by the physical spectral variable. -/
def polynomialOracle (N : ℕ) : Fin N → ℝ[X] → ℝ[X] := fun _ p => X * p

/-- Exact nominal recovery, including the separately initialized zero gradient. -/
theorem nominal_recovery (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) :
    (parameters I N).recoveredGradient s
      (if s.val = 0 then 0 else X * bezout.Flat.virtualPolynomial I (s.val-1))
      (X * physicalQuery I N s) = X * bezout.Flat.virtualPolynomial I s := by
  by_cases hs : s.val = 0
  · simp [FlatParameters.recoveredGradient, physicalQuery, parameters, hs,
      bezout.Flat.tau_zero I N (by omega)]
  · have hr := (parameters I N).recoveredGradient_linear s
      (ne_of_gt (denominator_pos I N hN s)) (LinearMap.mulLeft ℝ (X : ℝ[X]))
      (bezout.Flat.virtualPolynomial I s.val) (bezout.Flat.virtualPolynomial I (s.val-1))
    simpa only [hs, ite_false, LinearMap.mulLeft_apply, physicalQuery, parameters,
      Polynomial.smul_eq_C_mul] using hr

/-- The two virtual registers and gradient register throughout every nominal
prefix; the fourth register contains the preceding actual oracle answer. -/
theorem nominal_prefix (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (k : ℕ) (hk : k < N) :
    ∃ a : ℝ[X], ((program I N).runPrefix (polynomialOracle N) 1 k).vectors =
      ![bezout.Flat.virtualPolynomial I k,
        bezout.Flat.virtualPolynomial I (k-1),
        if k=0 then 0 else X * bezout.Flat.virtualPolynomial I (k-1), a] := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    simp [RegisterProgram.runPrefix, RegisterProgram.initialState, program,
      FlatParameters.program, bezout.Flat.virtualPolynomial_zero]
    ext i
    fin_cases i <;> simp
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih (by omega)
    have hstep := (parameters I N).stage_vectors ⟨k,by omega⟩
      (ne_of_gt (denominator_pos I N hN _)) (polynomialOracle N)
      (bezout.Flat.virtualPolynomial I k) (bezout.Flat.virtualPolynomial I (k-1))
      (if k=0 then 0 else X * bezout.Flat.virtualPolynomial I (k-1)) a
      (((program I N).runPrefix (polynomialOracle N) 1 k).calls)
    have hquery : bezout.Flat.virtualPolynomial I k + (parameters I N).tau ⟨k,by omega⟩ •
        (bezout.Flat.virtualPolynomial I k - bezout.Flat.virtualPolynomial I (k-1)) =
        physicalQuery I N k := by simp only [physicalQuery, parameters, Polynomial.smul_eq_C_mul]
    rw [hquery] at hstep
    simp only [polynomialOracle] at hstep
    rw [nominal_recovery I N hN ⟨k,by omega⟩] at hstep
    simp only [show k + 1 < N by omega, ite_true] at hstep
    have hnext :
        (1 + (parameters I N).beta ⟨k,by omega⟩) • bezout.Flat.virtualPolynomial I k -
        (parameters I N).beta ⟨k,by omega⟩ • bezout.Flat.virtualPolynomial I (k-1) -
        (parameters I N).alpha ⟨k,by omega⟩ • (X * bezout.Flat.virtualPolynomial I k) =
          bezout.Flat.virtualPolynomial I (k+1) := by
      simp only [parameters, Polynomial.smul_eq_C_mul]
      cases k with
      | zero => simp [bezout.Flat.beta, bezout.Flat.virtualPolynomial_one]
      | succ k =>
        simpa only [Nat.add_sub_cancel, Nat.add_assoc, mul_assoc] using
          (bezout.Flat.virtualPolynomial_step I k).symm
    rw [hnext] at hstep
    refine ⟨X * physicalQuery I N k, ?_⟩
    rw [RegisterProgram.runPrefix, dite_eq_left (show k < N by omega)]
    have hstate : (program I N).runPrefix (polynomialOracle N) 1 k =
        ⟨![bezout.Flat.virtualPolynomial I k, bezout.Flat.virtualPolynomial I (k-1),
          if k=0 then 0 else X * bezout.Flat.virtualPolynomial I (k-1),a],
          ((program I N).runPrefix (polynomialOracle N) 1 k).calls⟩ := by
      apply RegisterState.ext
      · exact ha
      · rfl
    rw [hstate]
    simpa only [program, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ite_false] using hstep

/-- The physical symbolic query is the article's extrapolated normalized U state. -/
theorem nominal_query (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (program I N).queryAt (polynomialOracle N) 1 s = physicalQuery I N s := by
  obtain ⟨a, ha⟩ := nominal_prefix I N hN s.val s.isLt
  unfold RegisterProgram.queryAt
  rw [ha]
  change executeLinear ((parameters I N).program.before s) _ _ = _
  rw [FlatParameters.before_vectors]
  simp only [program, FlatParameters.program, parameters, physicalQuery,
    Matrix.cons_val_zero, Polynomial.smul_eq_C_mul]

/-- The literal final assignment returns the prescribed Chebyshev residual. -/
theorem nominal_output (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (program I N).output (polynomialOracle N) 1 = I.residual N := by
  let k := N-1
  have hk : k < N := by dsimp [k]; omega
  obtain ⟨a, ha⟩ := nominal_prefix I N hN k hk
  have hstep := (parameters I N).stage_vectors ⟨k,hk⟩
    (ne_of_gt (denominator_pos I N hN _)) (polynomialOracle N)
    (bezout.Flat.virtualPolynomial I k) (bezout.Flat.virtualPolynomial I (k-1))
    (if k=0 then 0 else X * bezout.Flat.virtualPolynomial I (k-1)) a
    (((program I N).runPrefix (polynomialOracle N) 1 k).calls)
  have hquery : bezout.Flat.virtualPolynomial I k + (parameters I N).tau ⟨k,hk⟩ •
      (bezout.Flat.virtualPolynomial I k - bezout.Flat.virtualPolynomial I (k-1)) =
      physicalQuery I N k := by simp only [physicalQuery, parameters, Polynomial.smul_eq_C_mul]
  rw [hquery] at hstep
  simp only [polynomialOracle] at hstep
  rw [nominal_recovery I N hN ⟨k,hk⟩] at hstep
  simp only [show ¬ k+1<N by dsimp [k]; omega, ite_false] at hstep
  have hstate : (program I N).runPrefix (polynomialOracle N) 1 k =
      ⟨![bezout.Flat.virtualPolynomial I k, bezout.Flat.virtualPolynomial I (k-1),
        if k=0 then 0 else X * bezout.Flat.virtualPolynomial I (k-1),a],
        ((program I N).runPrefix (polynomialOracle N) 1 k).calls⟩ := by
    apply RegisterState.ext
    · exact ha
    · rfl
  have hout : (program I N).output (polynomialOracle N) 1 =
      (1 + bezout.Flat.terminalA I N) • bezout.Flat.virtualPolynomial I k -
      bezout.Flat.terminalA I N • bezout.Flat.virtualPolynomial I (k-1) -
      bezout.Flat.terminalB I N • (X * bezout.Flat.virtualPolynomial I k) := by
    unfold RegisterProgram.output RegisterProgram.run
    have hn : (program I N).runPrefix (polynomialOracle N) 1 N =
        (program I N).runPrefix (polynomialOracle N) 1 (k+1) := by
      congr 1
      dsimp [k]
      omega
    rw [hn, RegisterProgram.runPrefix, dite_eq_left hk, hstate]
    exact congrFun hstep 1
  rw [hout]
  simp only [Polynomial.smul_eq_C_mul, k, show N-1-1=N-2 by omega]
  simpa only [mul_assoc] using (bezout.Flat.virtualPolynomial_terminal I N hN).symm

/-- Physical-to-chart substitution recovers exactly the displayed Flat query. -/
theorem physicalQuery_comp_chart (I : chebyshev1.SpectralInterval) (N s : ℕ) :
    (physicalQuery I N s).comp (bezout.GradedFamily.chart I) =
      bezout.Flat.queryPolynomial I N s := by
  have hv (k : ℕ) : (bezout.Flat.virtualPolynomial I k).comp
      (bezout.GradedFamily.chart I) = bezout.Flat.normalizedU I k := by
    rw [bezout.Flat.virtualPolynomial, comp_assoc,
      bezout.GradedFamily.coordinate_comp_chart, comp_X]
  simp only [physicalQuery, add_comp, mul_comp, sub_comp, C_comp, hv,
    bezout.Flat.queryPolynomial, map_add, map_one]
  ring

/-- The literal four-vector program has exactly the synthesized Flat history.
Use: this identifies every physical response, not only the noiseless terminal. -/
theorem history_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (program I N).history (normalized I N hN) = bezout.Flat.history I N hN := by
  apply (bezout.Flat.queries I N (by omega)).realize_unique I
    (fun s => bezout.Flat.queryPolynomial_eta I N s)
  · change ((program I N).history (normalized I N hN)).terminal = I.residual N
    rw [← RegisterProgram.polynomial_output, ← nominal_output I N hN]
    rfl
  · intro s
    unfold bezout.History.chartQuery
    rw [← RegisterProgram.polynomial_query]
    change ((program I N).queryAt (polynomialOracle N) 1 s).comp _ = _
    rw [nominal_query I N hN s]
    exact physicalQuery_comp_chart I N s

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Every actual query of Algorithm 1 equals the Flat causal history query, for
an arbitrary time-dependent oracle and any actual sequence of returned errors. -/
theorem query_eq_history (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (program I N).queryAt oracle initial s =
      (bezout.Flat.history I N hN).oracleQuery initial oracle s := by
  rw [RegisterProgram.query_eq_history _ (normalized I N hN), history_eq]

/-- The actual physical output of Algorithm 1 equals the Flat history output for
every oracle stream. Use: all proved physical gains and risks apply to this code. -/
theorem output_eq_history (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (program I N).output oracle initial =
      (bezout.Flat.history I N hN).oracleOutput initial oracle := by
  rw [RegisterProgram.output_eq_history _ (normalized I N hN), history_eq]

/-- The recursively prepared implementation has the same output for every
actual oracle stream, including arbitrary errors in every returned answer. -/
theorem prepared_output_eq_history (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (preparedProgram I N).output oracle initial =
      (bezout.Flat.history I N hN).oracleOutput initial oracle := by
  rw [preparedProgram_eq I N hN, output_eq_history]

/-- Exact additive response of the physical four-vector algorithm for arbitrary
linear Hessians and actual error streams, with no stochastic restrictions. -/
theorem physical_response (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial : E) (noise : Fin N → E) :
    (program I N).output (fun s y => H y+noise s) initial =
      (Polynomial.aeval H (I.residual N)) initial +
      ∑ s, (Polynomial.aeval H ((bezout.Flat.history I N hN).response s)) (noise s) := by
  have he := bezout.Flat.history_exact I N hN
  change (bezout.Flat.history I N hN).terminal = I.residual N at he
  rw [output_eq_history, bezout.History.oracleOutput_linear,
    bezout.History.physical_response, he]

/-- Algorithm 1 makes exactly N actual oracle calls. -/
theorem oracle_calls (I : chebyshev1.SpectralInterval) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    ((program I N).run oracle initial).calls = N := RegisterProgram.run_calls _ _ _

omit [AddCommGroup E] [Module ℝ E] in
/-- The complete physical state of Algorithm 1 has four vector slots. -/
theorem vector_slots (I : chebyshev1.SpectralInterval) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) : Fintype.card (Fin 4) = 4 :=
  RegisterProgram.vector_slots (program I N) oracle initial

end
end bezout.Algorithms.Flat
