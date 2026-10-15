import «2610.05164v2».Finite.Inverse
import «2606.16671v2».Chebyshev.Coordinates

/-!
Article: 2610.05164v2, Theorem 2.1.
The genuine finite-horizon bijection of Theorem 2.1.
Use: `«2610.05164v2».recurrenceEquiv` feeds `«2610.05164v2».SineJacobi.symmetric_gain_exact`
(symmetric gain exact).
-/
namespace «2610.05164v2»
noncomputable section
open «2606.16671v2» Polynomial Polynomial.Chebyshev

/--
The precise assertion is `(fiberPolynomial N).Monic`.

Use: `«2610.05164v2».Recurrence.jacobi_terminal` rewrites with this assertion to establish the
precise assertion is `(R.jacobi I).Terminal`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_monic` with the arguments
shown in the proof.
-/
theorem fiberPolynomial_monic (N : ℕ) : (fiberPolynomial N).Monic := by
  apply «2606.16671v2».Prefix.jacobiData.block_monic
  intro i
  simp only [Prefix.jacobiData]
  split_ifs <;> norm_num

namespace Recurrence
variable {N : ℕ} (R : Recurrence N) (I : SpectralInterval)

/--
Exact identity `R = S`.

Use: `«2610.05164v2».Recurrence.recurrence_jacobi` uses this identity to establish exact
identity `(R.jacobi I).recurrence I (R.jacobi_admissible I) = R`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Separate `i < N` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem ext_of_agree {S : Recurrence N} (h : Horizon.Agree N R.method S.method) : R = S := by
  -- Separate `i < N` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply Recurrence.ext
  apply Horizon.twoTerm_ext
  · funext i; by_cases hi : i < N
    · exact (h i hi).1
    · rw [R.alpha_tail i (Nat.not_lt.mp hi), S.alpha_tail i (Nat.not_lt.mp hi)]
  · funext i; by_cases hi : i < N
    · exact (h i hi).2.1
    · rw [R.memory_tail i (Nat.not_lt.mp hi), S.memory_tail i (Nat.not_lt.mp hi)]
  · funext i; by_cases hi : i < N
    · exact (h i hi).2.2
    · rw [R.gamma_tail i (Nat.not_lt.mp hi), S.gamma_tail i (Nat.not_lt.mp hi)]

/--
Terminal exactness recovers the monic characteristic polynomial, not merely its zero set or its
values on the spectral interval.

The precise assertion is `(R.jacobi I).Terminal`.

Use: `«2610.05164v2».recurrenceEquiv` uses this assertion in the displayed construction of
`recurrenceEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem jacobi_terminal (hN : 0 < N) (ht : R.Terminal I) : (R.jacobi I).Terminal := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hr := (R.jacobi I).data.residualPolynomial_eq I (R.jacobi_admissible I) N le_rfl
  change ((R.jacobi I).data.method I).realization.residualPolynomial N =
    (R.jacobi I).data.residual I N at hr
  rw [Horizon.residual_eq (R.jacobi_method_agree I) le_rfl, ht] at hr
  have hp : (R.jacobi I).data.leading N = C (R.normalizer I N / I.den N)*T ℝ N := by
    apply Polynomial.funext
    intro x
    have he := congrArg (fun p : ℝ[X] => p.eval (I.lambda x)) hr
    rw [SpectralInterval.residual_eval, JacobiData.residual_eval, I.z_lambda,
      R.jacobi_den I N le_rfl] at he
    simp only [eval_mul, eval_C]
    field_simp [I.den_ne N, (R.normalizer_pos I N).ne'] at he ⊢
    exact he.symm
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let c : ℝ := (R.normalizer I (n+1)/I.den (n+1))/(1/2:ℝ)^n
  have hscale : (R.jacobi I).data.leading (n+1) = C c*fiberPolynomial (n+1) := by
    rw [hp, fiberPolynomial_succ, ← mul_assoc, ← map_mul]
    congr 1
    dsimp [c]
    rw [div_mul_cancel₀ _ (pow_ne_zero n (by norm_num : (1/2:ℝ) ≠ 0))]
  have hm : ((R.jacobi I).data.leading (n+1)).Monic :=
    (R.jacobi I).data.block_monic (R.jacobi I).coupling_nonneg 0 (n+1)
  have he := congrArg Polynomial.leadingCoeff hscale
  rw [hm.leadingCoeff, (fiberPolynomial_monic (n+1)).leadingCoeff_C_mul] at he
  change (R.jacobi I).data.leading (n+1) = fiberPolynomial (n+1)
  simpa [← he] using hscale

/--
Exact identity `(R.jacobi I).recurrence I (R.jacobi_admissible I) = R`.

Use: `«2610.05164v2».recurrenceEquiv` uses this identity in the displayed construction of
`recurrenceEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Recurrence.jacobi_admissible`,
`«2610.05164v2».Recurrence.ext_of_agree`, `«2610.05164v2».Jacobi.recurrence_agree` with the
arguments shown in the proof.
-/
theorem recurrence_jacobi :
    (R.jacobi I).recurrence I (R.jacobi_admissible I) = R := by
  apply ext_of_agree
  intro i hi
  obtain ⟨ha,hb,hg⟩ := (R.jacobi I).recurrence_agree I (R.jacobi_admissible I) i hi
  obtain ⟨ha',hb',hg'⟩ := R.jacobi_method_agree I i hi
  exact ⟨ha.trans ha', hb.trans hb', hg.trans hg'⟩

end Recurrence

namespace Jacobi
variable {N : ℕ} (J : Jacobi N) (I : SpectralInterval)

/--
Recovering the diagonal and incoming coupling from the forward coefficients.

Exact identity `(J.recurrence I h).jacobi I = J`.

Use: `«2610.05164v2».recurrenceEquiv` uses this identity in the displayed construction of
`recurrenceEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Separate `i < N` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity. Prove equality of functions by evaluating both sides
at an arbitrary argument.
-/
theorem jacobi_recurrence (h : J.data.Admissible I N) : (J.recurrence I h).jacobi I = J := by
  -- Separate `i < N` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply Jacobi.ext
  apply Horizon.jacobiData_ext
  · funext i
    by_cases hi : i < N
    · change (if i < N then I.eta-(J.recurrence I h).alpha i /
        (J.recurrence I h).scale I i else 0) = J.data.b i
      simp only [hi, ite_true, Recurrence.alpha, Recurrence.scale, Recurrence.gamma,
        recurrence, Horizon.truncate, JacobiData.method]
      field_simp [(h i (by omega)).ne', (h (i+1) (by omega)).ne', I.delta_pos.ne']
      ring
    · simp [Recurrence.jacobi, Horizon.restrictData, hi, J.diagonal_tail i (Nat.not_lt.mp hi)]
  · funext i
    by_cases hi : i < N
    · by_cases h0 : i = 0
      · subst i; simp [Recurrence.jacobi, Horizon.restrictData, Recurrence.inverseData,
          J.coupling_zero]
      · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
        change (if j+1 < N then
          (if j+1 = 0 then 0 else (J.recurrence I h).beta (j+1) /
            ((J.recurrence I h).scale I (j+1)*(J.recurrence I h).scale I j)) else 0) = _
        simp only [show j+1 < N by omega, show j < N by omega, show j+1 ≠ 0 by omega,
          ite_true, ite_false, Recurrence.beta, Recurrence.scale, Recurrence.gamma,
          recurrence, Horizon.truncate, JacobiData.method, neg_neg, Nat.add_sub_cancel]
        field_simp [(h j (by omega)).ne', (h (j+1) (by omega)).ne',
          (h (j+2) (by omega)).ne', I.delta_pos.ne']
    · simp [Recurrence.jacobi, Horizon.restrictData, hi, J.coupling_tail i (Nat.not_lt.mp hi)]

end Jacobi

/--
The genuine finite-horizon bijection of Theorem 2.1.

Use: `«2610.05164v2».Optimal.finiteGain_le_sine` uses this definition to establish the stated
quantitative bound `finiteGain I n ≤ 2*sqrt (SineJacobi.chain (n+1)).normalizedEnergy`.

Article: 2610.05164v2, Theorem 2.1.
-/
def recurrenceEquiv (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    Fiber N ≃ ExactRecurrence I N where
  toFun J := ⟨J.val.recurrence I (J.val.admissible I hN J.property),
    J.val.recurrence_terminal I hN J.property⟩
  invFun R := ⟨R.val.jacobi I, R.val.jacobi_terminal I hN R.property⟩
  left_inv J := by
    apply Subtype.ext
    exact J.val.jacobi_recurrence I (J.val.admissible I hN J.property)
  right_inv R := by apply Subtype.ext; exact R.val.recurrence_jacobi I

end
end «2610.05164v2»
