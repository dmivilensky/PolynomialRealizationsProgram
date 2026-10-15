import «2610.05164v2».Finite.Restriction

/-!
Article: 2610.05164v2, Theorem 2.1.
All leading determinants at z_0 are the positive normalization products.
Use: `«2610.05164v2».Recurrence.jacobi_method_agree` feeds
`«2610.05164v2».Recurrence.recurrence_jacobi` (recurrence jacobi).
Proof chain: `«2610.05164v2».recurrenceEquiv` — 2610.05164v2, Theorem 2.1; Bijection with all
admissible Jacobi matrices, including reducible matrices.
-/
namespace «2610.05164v2».Recurrence
noncomputable section
open «2606.16671v2» Polynomial
open scoped BigOperators
variable {N : ℕ} (R : Recurrence N) (I : SpectralInterval)

/--
The normalized stepsize a_j=Delta gamma_j/2 in Appendix A.1.

Use: `«2610.05164v2».Recurrence.inverseData` uses this definition in the displayed construction
of `inverseData`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.
-/
def scale (i : ℕ) : ℝ := I.delta * R.gamma i / 2
/--
The stated quantitative bound `0 < R.scale I i`.

Use: `«2610.05164v2».Recurrence.inverseData_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ (R.inverseData I).aSq i`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem scale_pos (i : ℕ) : 0 < R.scale I i :=
  div_pos (mul_pos I.delta_pos (R.gamma_pos i)) (by norm_num)

/--
Defines `normalizer` of type `ℝ` by `∏ i ∈ Finset.range n, (R.scale I i)⁻¹`.

Use: `«2610.05164v2».Recurrence.inverse_den` uses this definition to establish the identity
`(R.inverseData I).den I n = R.normalizer I n`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.
-/
def normalizer (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (R.scale I i)⁻¹
/--
Exact identity `R.normalizer I 0 = 1`.

Use: `«2610.05164v2».Recurrence.inverse_den` rewrites with this identity to establish exact
identity `(R.inverseData I).den I n = R.normalizer I n`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem normalizer_zero : R.normalizer I 0 = 1 := by simp [normalizer]
/--
Exact identity `R.normalizer I (n+1) = R.normalizer I n / R.scale I n`.

Use: `«2610.05164v2».Recurrence.inverse_den` rewrites with this identity to establish exact
identity `(R.inverseData I).den I n = R.normalizer I n`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizer_succ (n : ℕ) :
    R.normalizer I (n+1) = R.normalizer I n / R.scale I n := by
  simp [normalizer, Finset.prod_range_succ, div_eq_mul_inv, mul_comm]
/--
The stated quantitative bound `0 < R.normalizer I n`.

Use: `«2610.05164v2».Recurrence.inverse_method` uses this bound to establish the identity
`(R.inverseData I).method I = R.method`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Recurrence.scale_pos` with the arguments
shown in the proof.
-/
theorem normalizer_pos (n : ℕ) : 0 < R.normalizer I n :=
  Finset.prod_pos (fun i _ => inv_pos.mpr (R.scale_pos I i))

/--
The inverse coefficient formulas, before restriction to the finite horizon.

Use: `«2610.05164v2».Recurrence.inverseData_nonneg` uses this definition to establish the
stated quantitative bound `0 ≤ (R.inverseData I).aSq i`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.
-/
def inverseData : JacobiData where
  b i := I.eta - R.alpha i / R.scale I i
  aSq i := if i = 0 then 0 else R.beta i / (R.scale I i * R.scale I (i-1))

/--
The stated quantitative bound `0 ≤ (R.inverseData I).aSq i`.

Use: `«2610.05164v2».Recurrence.jacobi` uses this bound in the displayed construction of
`jacobi`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Recurrence.beta_nonneg`,
`«2610.05164v2».Recurrence.scale_pos` with the arguments shown in the proof.
-/
theorem inverseData_nonneg (i : ℕ) : 0 ≤ (R.inverseData I).aSq i := by
  dsimp [inverseData]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (R.beta_nonneg i)
      (mul_pos (R.scale_pos I i) (R.scale_pos I (i-1))).le

/--
Exact identity `R.alpha 0 = 1`.

Use: `«2610.05164v2».Recurrence.inverse_den` rewrites with this identity to establish exact
identity `(R.inverseData I).den I n = R.normalizer I n`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem alpha_zero : R.alpha 0 = 1 := by simpa [alpha, R.memory_zero] using R.normalized 0

/--
All leading determinants at z_0 are the positive normalization products.

Exact identity `(R.inverseData I).den I n = R.normalizer I n`.

Use: `«2610.05164v2».Recurrence.inverse_method` rewrites with this identity to establish exact
identity `(R.inverseData I).method I = R.method`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Clear the
denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem inverse_den (n : ℕ) : (R.inverseData I).den I n = R.normalizer I n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [JacobiData.den_one, normalizer_succ, normalizer_zero]
    simp [inverseData, R.alpha_zero]
  | more n ih0 ih1 =>
    rw [JacobiData.den_add_two, ih0, ih1]
    simp only [inverseData, show n+1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
    rw [R.normalizer_succ I (n+1), R.normalizer_succ I n]
    have hnorm : R.alpha (n+1)-R.beta (n+1) = 1 := by
      simpa [alpha, beta] using R.normalized (n+1)
    field_simp [(R.scale_pos I n).ne', (R.scale_pos I (n+1)).ne']
    linear_combination R.normalizer I n * hnorm

/--
Exact identity `(R.inverseData I).method I = R.method`.

Use: `«2610.05164v2».Recurrence.jacobi_method_agree` rewrites with this identity to establish
the precise assertion is `Horizon.Agree N ((R.jacobi I).data.method I) R.method`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Separate `i = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity. Prove equality of functions by evaluating both sides
at an arbitrary argument.
-/
theorem inverse_method : (R.inverseData I).method I = R.method := by
  -- Separate `i = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply Horizon.twoTerm_ext
  · funext i
    simp only [JacobiData.method, inverse_den]
    change R.normalizer I i / R.normalizer I (i+1) *
      (I.eta-(I.eta-R.alpha i / R.scale I i)) = R.alpha i
    rw [normalizer_succ]
    field_simp [(R.normalizer_pos I i).ne', (R.scale_pos I i).ne']
    ring
  · funext i
    simp only [JacobiData.method, inverse_den]
    change -((if i = 0 then 0 else R.beta i / (R.scale I i * R.scale I (i-1))) *
      R.normalizer I (i-1) / R.normalizer I (i+1)) = R.method.b i
    by_cases hi : i = 0
    · subst i; simp [R.memory_zero]
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
        show j+1 ≠ 0 by omega, ite_false]
      rw [normalizer_succ, normalizer_succ]
      simp only [beta]
      field_simp [(R.normalizer_pos I j).ne', (R.scale_pos I j).ne',
        (R.scale_pos I (j+1)).ne']
  · funext i
    simp only [JacobiData.method, inverse_den]
    rw [normalizer_succ]
    change _ = R.gamma i
    unfold scale
    field_simp [(R.normalizer_pos I i).ne', (R.gamma_pos i).ne', I.delta_pos.ne']

/--
Constructs `jacobi` of type `Jacobi N` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Recurrence.jacobi_den` rewrites with this definition to establish exact
identity `(R.jacobi I).data.den I n = R.normalizer I n`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.
-/
def jacobi : Jacobi N where
  data := Horizon.restrictData N (R.inverseData I)
  coupling_nonneg i := by
    dsimp [Horizon.restrictData]; split_ifs
    · exact R.inverseData_nonneg I i
    · exact le_rfl
  coupling_zero := by simp [Horizon.restrictData, inverseData]
  diagonal_tail i hi := by simp [Horizon.restrictData, Nat.not_lt.mpr hi]
  coupling_tail i hi := by simp [Horizon.restrictData, Nat.not_lt.mpr hi]

/--
Exact identity `(R.jacobi I).data.den I n = R.normalizer I n`.

Use: `«2610.05164v2».Recurrence.jacobi_admissible` rewrites with this identity to establish the
precise assertion is `(R.jacobi I).data.Admissible I N`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Horizon.restrict_den`,
`«2610.05164v2».Recurrence.inverse_den` with the arguments shown in the proof.
-/
theorem jacobi_den (n : ℕ) (hn : n ≤ N) :
    (R.jacobi I).data.den I n = R.normalizer I n := by rw [jacobi, Horizon.restrict_den N (R.inverseData I) I n hn, inverse_den]

/--
The precise assertion is `(R.jacobi I).data.Admissible I N`.

Use: `«2610.05164v2».Recurrence.jacobi_terminal` uses this assertion to establish the precise
assertion is `(R.jacobi I).Terminal`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Recurrence.jacobi_den`,
`«2610.05164v2».Recurrence.normalizer_pos` with the arguments shown in the proof.
-/
theorem jacobi_admissible : (R.jacobi I).data.Admissible I N := by intro n hn; rw [R.jacobi_den I n hn]; exact R.normalizer_pos I n

/--
The precise assertion is `Horizon.Agree N ((R.jacobi I).data.method I) R.method`.

Use: `«2610.05164v2».Recurrence.jacobi_terminal` rewrites with this assertion to establish the
precise assertion is `(R.jacobi I).Terminal`.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Horizon.restrict_method_agree`,
`«2610.05164v2».Recurrence.inverse_method` with the arguments shown in the proof.
-/
theorem jacobi_method_agree : Horizon.Agree N ((R.jacobi I).data.method I) R.method := by
  have h := Horizon.restrict_method_agree N (R.inverseData I) I
  rw [R.inverse_method I] at h
  exact h

end
end «2610.05164v2».Recurrence
