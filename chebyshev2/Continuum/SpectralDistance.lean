import chebyshev2.Continuum.ReferenceSpectrum

/-!
Article: chebyshev2, Theorem 2.4.
The finite-spectrum contribution to equation (8), in the l1 norm.
Use: `chebyshev2.Continuum.finite_reference_distance_bound` feeds
`chebyshev2.Packing.packed_reference_distance` (Theorem 2.4, equation (8)).
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/--
Summability of the displayed sequence: `Summable (finiteEigenvalue N)`.

Use: `chebyshev2.Continuum.finite_reference_distance` uses this summability result to
establish exact identity `(∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) = 2 * ∑' j,
referenceEigenvalue (j + N)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `chebyshev2.Continuum.finiteEigenvalue_nonneg`,
`chebyshev2.Continuum.finiteEigenvalue_le`, `chebyshev2.Continuum.summable_dominator`
with the arguments shown in the proof.
-/
theorem finiteEigenvalue_summable (N : ℕ) : Summable (finiteEigenvalue N) :=
  summable_dominator.of_nonneg_of_le (finiteEigenvalue_nonneg N) (finiteEigenvalue_le N)

/--
The stated quantitative bound `referenceEigenvalue j ≤ 4 / Real.pi ^ 2 * (1 / (2 * (j : ℝ) - 1)
- 1 / (2 * (j : ℝ) + 1))`.

Use: `chebyshev2.Continuum.reference_tail_partial` uses this bound to establish the stated
quantitative bound `(∑ j ∈ Finset.range M, referenceEigenvalue (j + N)) ≤ 4 / Real.pi ^ 2 * (1
/ (2 * (N : ℝ) - 1) - 1 / (2 * (N + M : ℕ) - 1))`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.finite_reference_distance_bound`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem reference_tail_term {j : ℕ} (hj : 0 < j) : referenceEigenvalue j ≤
    4 / Real.pi ^ 2 * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold referenceEigenvalue
  have h₁ : 0 < 2 * (j : ℝ) - 1 := by linarith
  have h₂ : 0 < 2 * (j : ℝ) + 1 := by positivity
  field_simp
  nlinarith [sq_pos_of_pos Real.pi_pos]

/--
The stated quantitative bound `(∑ j ∈ Finset.range M, referenceEigenvalue (j + N)) ≤ 4 /
Real.pi ^ 2 * (1 / (2 * (N : ℝ) - 1) - 1 / (2 * (N + M : ℕ) - 1))`.

Use: `chebyshev2.Continuum.reference_tail_bound` uses this bound to establish the stated
quantitative bound `(∑' j, referenceEigenvalue (j + N)) ≤ 4 / (Real.pi ^ 2 * (2 * (N : ℝ) -
1))`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.finite_reference_distance_bound`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `M`; the recursive step uses the previous-stage assertion.
-/
theorem reference_tail_partial {N : ℕ} (hN : 0 < N) (M : ℕ) :
    (∑ j ∈ Finset.range M, referenceEigenvalue (j + N)) ≤
      4 / Real.pi ^ 2 * (1 / (2 * (N : ℝ) - 1) - 1 / (2 * (N + M : ℕ) - 1)) := by
  -- Induct on `M`; the recursive step uses the previous-stage assertion.
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hh := reference_tail_term (j := M + N) (by omega)
    have he : (2 * (M + N : ℕ) + 1 : ℝ) = 2 * (N + M + 1 : ℕ) - 1 := by
      simp only [Nat.cast_add, Nat.cast_one]; ring
    have he' : (M + N : ℕ) = N + M := by omega
    rw [he, he'] at hh
    rw [he']
    simp only [Nat.cast_add, Nat.cast_one] at ih hh ⊢
    simp only [add_assoc] at hh
    linarith

/--
The stated quantitative bound `(∑' j, referenceEigenvalue (j + N)) ≤ 4 / (Real.pi ^ 2 * (2 * (N
: ℝ) - 1))`.

Use: `chebyshev2.Continuum.finite_reference_distance_bound` uses this bound to establish
the stated quantitative bound `(∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) ≤ 8 /
(Real.pi ^ 2 * (2 * (N : ℝ) - 1))`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.finite_reference_distance_bound`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem reference_tail_bound {N : ℕ} (hN : 0 < N) :
    (∑' j, referenceEigenvalue (j + N)) ≤ 4 / (Real.pi ^ 2 * (2 * (N : ℝ) - 1)) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  have hs := summable_reference.comp_injective (show Function.Injective (fun j : ℕ => j + N)
    from fun _ _ h => by dsimp at h; omega)
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro M
  simp only [Function.comp_apply]
  have h := reference_tail_partial hN M
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < 2 * (N + M : ℕ) - (1 : ℝ) := by
    have hle : (N : ℝ) ≤ N + M := by exact_mod_cast (Nat.le_add_right N M)
    simp only [Nat.cast_add]
    linarith
  have hp : 0 ≤ 4 / Real.pi ^ 2 * (1 / (2 * (N + M : ℕ) - 1)) := by positivity
  have he : 4 / Real.pi ^ 2 * (1 / (2 * (N : ℝ) - 1)) =
      4 / (Real.pi ^ 2 * (2 * (N : ℝ) - 1)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [mul_sub, he] at h
  linarith

/--
Exact identity `(∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) = 2 * ∑' j,
referenceEigenvalue (j + N)`.

Use: `chebyshev2.Continuum.finite_reference_distance_bound` rewrites with this identity to
establish the stated quantitative bound `(∑' j, |finiteEigenvalue N j - referenceEigenvalue j|)
≤ 8 / (Real.pi ^ 2 * (2 * (N : ℝ) - 1))`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.finite_reference_distance_bound`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem finite_reference_distance {N : ℕ} (hN : 0 < N) :
    (∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) =
      2 * ∑' j, referenceEigenvalue (j + N) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hs := ((finiteEigenvalue_summable N).sub summable_reference).abs
  have hhead : (∑ j ∈ Finset.range N, |finiteEigenvalue N j - referenceEigenvalue j|) =
      1 - ∑ j ∈ Finset.range N, referenceEigenvalue j := by
    have he (j : ℕ) (hj : j ∈ Finset.range N) :
        |finiteEigenvalue N j - referenceEigenvalue j| = finiteEigenvalue N j - referenceEigenvalue j :=
      abs_of_nonneg (sub_nonneg.mpr (finiteEigenvalue_bounds (Finset.mem_range.mp hj)).1)
    rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    exact finiteEigenvalue_sum hN
  have htail : (fun j => |finiteEigenvalue N (j + N) - referenceEigenvalue (j + N)|) =
      (fun j => referenceEigenvalue (j + N)) := by
    funext j
    simp [finiteEigenvalue, show ¬j + N < N by omega, abs_of_pos (referenceEigenvalue_pos _)]
  have href := summable_reference.sum_add_tsum_nat_add N
  rw [reference_mass] at href
  have he := hs.sum_add_tsum_nat_add N
  rw [hhead, htail] at he
  linarith

/--
The finite-spectrum contribution to equation (8), in the l1 norm.

The stated quantitative bound `(∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) ≤ 8 /
(Real.pi ^ 2 * (2 * (N : ℝ) - 1))`.

Use: `chebyshev2.Packing.packed_reference_distance` uses this bound to establish the stated
quantitative bound `(∑' j, |packedEigenvalue J hN ht j-referenceEigenvalue j|) ≤ transferError
N`.

Article: chebyshev2, Theorem 2.4.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `chebyshev2.Continuum.finite_reference_distance`,
`chebyshev2.Continuum.reference_tail_bound` with the arguments shown in the proof.
-/
theorem finite_reference_distance_bound {N : ℕ} (hN : 0 < N) :
    (∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) ≤
      8 / (Real.pi ^ 2 * (2 * (N : ℝ) - 1)) := by
  rw [finite_reference_distance hN]
  convert mul_le_mul_of_nonneg_left (reference_tail_bound hN) (by norm_num : (0 : ℝ) ≤ 2) using 1
  ring

end
end chebyshev2.Continuum
