import «2606.16671v2».SineJacobi.Fourier
import «2606.16671v2».Jacobi.Admissibility
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
Article: 2606.16671v2, Lemma E.7.
The finite sine chain is terminal-Chebyshev exact, proved from its explicit coefficients.
Use: `«2606.16671v2».SineJacobi.admissible` feeds `«2606.16671v2».SineJacobi.quadraticError_exact`
(Terminal exactness for the independently defined iterates of Algorithm 2).
Proof chain: `«2606.16671v2».SineJacobi.gain_exact` — 2606.16671v2, Theorem 5.2; Exact sine gain,
resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Polynomial Real
open Polynomial.Chebyshev (T)
open scoped BigOperators

/--
Exact identity `(2:ℝ)^N*((data N).leading N).eval (cos theta) = 2*cos ((N:ℝ)*theta)`.

Use: `«2606.16671v2».SineJacobi.terminal` uses this identity to establish the identity `(data
N).leading N = C (2/(2:ℝ)^N)*T ℝ N`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.rogers_terminal`,
`«2606.16671v2».SineJacobi.cosineTransform_monomial`, `«2606.16671v2».SineJacobi.data_aSq` with
the arguments shown in the proof.
-/
theorem terminal_cosine (N : ℕ) (hN : 2 ≤ N) (theta : ℝ) :
    (2:ℝ)^N*((data N).leading N).eval (cos theta) = 2*cos ((N:ℝ)*theta) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.rogers_terminal`,
  -- `«2606.16671v2».SineJacobi.cosineTransform_monomial`, `«2606.16671v2».SineJacobi.data_aSq`
  -- with the arguments shown in the proof.
  have hf := congrArg (cosineTransform (N:ℤ) theta) (rogers_terminal N hN)
  have hn1 : (N:ℤ) = ((N-1:ℕ):ℤ)+1 := by omega
  rw [hn1, cosineTransform_recurrence] at hf
  rw [show ((N-1:ℕ):ℤ)-1 = ((N-2:ℕ):ℤ) by omega,
    ← leading_cosineTransform N (N-1) (by omega),
    ← leading_cosineTransform N (N-2) (by omega)] at hf
  rw [← hn1, map_add, cosineTransform_one] at hf
  have hpow : cosineTransform (N:ℤ) theta (X^N) = cos (-(N:ℝ)*theta) := by
    have hh := cosineTransform_monomial (N:ℤ) theta 1 N
    rw [← C_mul_X_pow_eq_monomial, C_1, one_mul] at hh
    simpa only [one_mul, Int.cast_natCast, show (N:ℝ)-2*(N:ℝ) = -(N:ℝ) by ring] using hh
  rw [hpow, neg_mul, cos_neg, Int.cast_natCast, ← two_mul] at hf
  have hr : (data N).leading N = X*(data N).leading (N-1) -
      C (couplingSq N (N-1))*(data N).leading (N-2) := by
    have hr0 : (data N).leading ((N-2)+2) = X*(data N).leading ((N-2)+1) -
        C ((data N).aSq ((N-2)+1))*(data N).leading (N-2) := by
      simp only [JacobiData.leading, JacobiData.block, data_b, C_0, sub_zero, Nat.zero_add]
    simpa only [show N-2+2 = N by omega, show N-2+1 = N-1 by omega,
      data_aSq N (N-1) (by omega) (by omega)] using hr0
  have hp1 : (2:ℝ)^N = 2^(N-1)*2 := by rw [← pow_succ]; congr 1; omega
  have hp2 : (2:ℝ)^(N-1) = 2^(N-2)*2 := by rw [← pow_succ]; congr 1; omega
  rw [hr]
  simp only [eval_sub, eval_mul, eval_X, eval_C]
  rw [hp1, hp2]
  rw [hp2] at hf
  linear_combination hf

/--
The finite sine chain is terminal-Chebyshev exact, proved from its explicit coefficients.

Exact identity `(data N).leading N = C (2/(2:ℝ)^N)*T ℝ N`.

Use: `«2606.16671v2».SineJacobi.spectrum_eq_nodes` rewrites with this identity to establish
exact identity `spectrum ℝ ((data N).matrix 0 N) = Set.range (fun k : Fin N => cos
((2*(k:ℝ)+1)*π/(2*(N:ℝ))))`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Separate `N = 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem terminal (N : ℕ) (hN : 0 < N) :
    (data N).leading N = C (2/(2:ℝ)^N)*T ℝ N := by
  -- Separate `N = 1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases h1 : N = 1
  · subst N
    simp [JacobiData.leading_one]
  · have h2 : 2 ≤ N := by omega
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Icc_infinite (by norm_num : (-1:ℝ) < 1)).mono
    intro x hx
    change ((data N).leading N).eval x = (C (2/(2:ℝ)^N)*T ℝ N).eval x
    have he := terminal_cosine N h2 (arccos x)
    rw [cos_arccos hx.1 hx.2] at he
    have ht : (T ℝ N).eval x = cos ((N:ℝ)*arccos x) := by
      calc _ = (T ℝ N).eval (cos (arccos x)) := by rw [cos_arccos hx.1 hx.2]
           _ = _ := by rw [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]
    rw [eval_mul, eval_C, ht]
    apply (mul_left_cancel₀ (pow_ne_zero N (by norm_num : (2:ℝ) ≠ 0)))
    rw [he]
    field_simp

/--
Exact identity `spectrum ℝ ((data N).matrix 0 N) = Set.range (fun k : Fin N => cos
((2*(k:ℝ)+1)*π/(2*(N:ℝ))))`.

Use: `«2606.16671v2».SineJacobi.spectrum_subset` rewrites with this identity to establish the
precise assertion is `spectrum ℝ ((data N).matrix 0 N) ⊆ Set.Icc (-1) 1`.

Article: 2606.16671v2, Theorem E.1.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly`,
`«2606.16671v2».SineJacobi.data_aSq_nonneg`, `«2606.16671v2».SineJacobi.terminal` with the
arguments shown in the proof.
-/
theorem spectrum_eq_nodes (N : ℕ) (hN : 0 < N) :
    spectrum ℝ ((data N).matrix 0 N) =
      Set.range (fun k : Fin N => cos ((2*(k:ℝ)+1)*π/(2*(N:ℝ)))) := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly`,
  -- `«2606.16671v2».SineJacobi.data_aSq_nonneg`, `«2606.16671v2».SineJacobi.terminal` with the
  -- arguments shown in the proof.
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, ← JacobiData.block_eq_charpoly _ (data_aSq_nonneg N),
    ← JacobiData.leading, terminal N hN]
  simp only [IsRoot, eval_mul, eval_C, mul_eq_zero,
    div_ne_zero (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero N (by norm_num : (2:ℝ) ≠ 0)), false_or]
  rw [← IsRoot, ← mem_roots (Polynomial.Chebyshev.T_ne_zero ℝ N), Polynomial.Chebyshev.roots_T_real]
  simp only [Finset.mem_val, Finset.mem_image, Finset.mem_range, Set.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k,hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.isLt, rfl⟩

/--
The precise assertion is `spectrum ℝ ((data N).matrix 0 N) ⊆ Set.Icc (-1) 1`.

Use: `«2606.16671v2».SineJacobi.admissible` uses this assertion to establish the precise
assertion is `(data N).Admissible I N`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.spectrum_eq_nodes` with the
arguments shown in the proof.
-/
theorem spectrum_subset (N : ℕ) (hN : 0 < N) :
    spectrum ℝ ((data N).matrix 0 N) ⊆ Set.Icc (-1) 1 := by
  rw [spectrum_eq_nodes N hN]
  rintro _ ⟨k,rfl⟩
  exact ⟨neg_one_le_cos _, cos_le_one _⟩

/--
The precise assertion is `(data N).Admissible I N`.

Use: `«2606.16671v2».SineJacobi.G_exact` uses this assertion to establish the identity `(data
N).G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.admissible_of_spectrum`,
`«2606.16671v2».SineJacobi.data_aSq_nonneg`, `«2606.16671v2».SineJacobi.spectrum_subset` with
the arguments shown in the proof.
-/
theorem admissible (I : SpectralInterval) (N : ℕ) (hN : 0 < N) : (data N).Admissible I N :=
  (data N).admissible_of_spectrum I N (data_aSq_nonneg N) (spectrum_subset N hN)

end
end «2606.16671v2».SineJacobi
