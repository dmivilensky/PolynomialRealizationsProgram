import bezout.Algorithms.Prediction
import bezout.Algorithms.BalancedPreparation

/-!
Article: bezout, Algorithm 2 and Appendix C's physical prediction proof.
Use: the printed six-vector program implements the actual Balanced history for
every oracle stream, with one call per stage and all startup indices included.
Proof: the proved scalar impulse table and normalizer recurrence satisfy the
generic prediction invariant; the output register accumulates the actual readout.
-/

namespace bezout.Algorithms.Balanced
noncomputable section
open scoped BigOperators

/-- The exact local scalar table used by the six-vector physical loop.
Only four consecutive impulse entries and four scalar prediction weights are read.
The separate scalar preparation theorems identify these entries with Algorithm 2. -/
def parameters (I : chebyshev1.SpectralInterval) (N : ℕ) (_hN : 2 ≤ N) : BalancedParameters N where
  weights k :=
    ![bezout.Balanced.recurrenceC N k.val * preparedNormalizer I N k.val /
        preparedNormalizer I N (k.val+4),
      -bezout.Balanced.recurrenceA I N k.val * preparedNormalizer I N (k.val+1) /
        preparedNormalizer I N (k.val+4),
      (1-bezout.Balanced.recurrenceC N k.val) * preparedNormalizer I N (k.val+2) /
        preparedNormalizer I N (k.val+4),
      bezout.Balanced.recurrenceA I N k.val * preparedNormalizer I N (k.val+3) /
        preparedNormalizer I N (k.val+4)]
  impulse j k := preparedImpulse I N j k.val / preparedNormalizer I N j
  readout k := preparedReadout I N k.val

/-- Algorithm 2 as six actual physical registers v0,v1,v2,v3,X,G. -/
def program (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : RegisterProgram 6 N :=
  (parameters I N hN).program

/-- Every local table entry is compatible with the actual Balanced causal history. -/
theorem compatible (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (parameters I N hN).Compatible (bezout.Balanced.history I N hN) where
  impulse k j hj := by
    have hz := ne_of_gt (bezout.Balanced.normalizer_pos I hN hj)
    change preparedImpulse I N j k.val / preparedNormalizer I N j = _
    rw [preparedNormalizer_eq]
    rw [preparedImpulse_eq I N hN ⟨j,hj⟩ k]
    unfold bezout.Balanced.impulse
    field_simp
  readout := by funext k; exact preparedReadout_eq I N hN k
  affine k hk := by
    have hz := ne_of_gt (bezout.Balanced.normalizer_pos I hN hk)
    have hr := bezout.Balanced.normalizer_fourth_order I hN hk
    change bezout.Balanced.normalizer I N (k.val+4) =
      bezout.Balanced.recurrenceA I N k.val * bezout.Balanced.normalizer I N (k.val+3) +
      (1-bezout.Balanced.recurrenceC N k.val) * bezout.Balanced.normalizer I N (k.val+2) -
      bezout.Balanced.recurrenceA I N k.val * bezout.Balanced.normalizer I N (k.val+1) +
      bezout.Balanced.recurrenceC N k.val * bezout.Balanced.normalizer I N k.val at hr
    simp [parameters, preparedNormalizer_eq, Fin.sum_univ_succ]
    field_simp
    linear_combination -hr
  past k hk i hi := by
    have hz := ne_of_gt (bezout.Balanced.normalizer_pos I hN hk)
    have hr := bezout.Balanced.impulse_recurrence I hN hk i
    have h3 : i.val ≠ k.val+3 := by omega
    have h1 : i.val ≠ k.val+1 := by omega
    simp only [ite_eq_right h3, ite_eq_right h1, mul_zero, sub_self, sub_zero,
      bezout.Balanced.impulse] at hr
    simp [parameters, preparedNormalizer_eq, Fin.sum_univ_succ]
    field_simp
    linear_combination -hr

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- All four live physical predictions equal the actual history's queries with
future answers set to zero, for every time-dependent actual oracle stream. -/
theorem prediction_register (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (k : ℕ) (hk : k ≤ N)
    (r : Fin 4) (hr : k+r.val<N) :
    ((program I N hN).runPrefix oracle initial k).vectors ⟨r.val,by omega⟩ =
      (bezout.Balanced.history I N hN).prediction initial
        ((program I N hN).answerAt oracle initial) ⟨k+r.val,hr⟩ k := by
  rw [RegisterProgram.runPrefix_eq_tape]
  exact ((parameters I N hN).prediction_invariant _ (compatible I N hN)
    initial _ k hk).predictions r hr

/-- Every physical oracle query of Algorithm 2 equals the actual Balanced query. -/
theorem query_eq_history (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (program I N hN).queryAt oracle initial s =
      (bezout.Balanced.history I N hN).oracleQuery initial oracle s :=
  (parameters I N hN).query_eq_history _ (compatible I N hN) oracle initial s

/-- The physical six-slot output equals the actual Balanced history on every
oracle stream. Use: every physical gain and perturbation theorem applies. -/
theorem output_eq_history (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (program I N hN).output oracle initial =
      (bezout.Balanced.history I N hN).oracleOutput initial oracle :=
  (parameters I N hN).output_eq_history _ (compatible I N hN) oracle initial

/-- Exact additive response of the physical six-vector algorithm for every
linear Hessian and every actual error stream, without independence assumptions. -/
theorem physical_response (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial : E) (noise : Fin N → E) :
    (program I N hN).output (fun s y => H y+noise s) initial =
      (Polynomial.aeval H (I.residual N)) initial +
      ∑ s, (Polynomial.aeval H ((bezout.Balanced.history I N hN).response s)) (noise s) := by
  have he := bezout.Balanced.history_exact I N hN
  change (bezout.Balanced.history I N hN).terminal = I.residual N at he
  rw [output_eq_history, bezout.History.oracleOutput_linear,
    bezout.History.physical_response, he]

/-- Exactly N actual oracle calls are made by Algorithm 2. -/
theorem oracle_calls (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    ((program I N hN).run oracle initial).calls = N := RegisterProgram.run_calls _ _ _

omit [AddCommGroup E] [Module ℝ E] in
/-- The complete physical state of Algorithm 2 consists of six vectors. -/
theorem vector_slots (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) : Fintype.card (Fin 6) = 6 :=
  RegisterProgram.vector_slots (program I N hN) oracle initial

/-- The scalar impulse band has four stored entries per row, hence linear storage. -/
theorem scalar_impulse_slots (N : ℕ) : Fintype.card (Fin N × Fin 4) = 4*N := by
  simp [mul_comm]

end
end bezout.Algorithms.Balanced
