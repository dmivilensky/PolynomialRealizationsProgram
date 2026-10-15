import «2606.16671v2».Chebyshev.Normalization
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

/-!
Article: 2606.16671v2, Theorem C.1.
Equality on the nondegenerate spectral interval is polynomial equality.
Use: `«2606.16671v2».SpectralInterval.residual_ne_zero` feeds `«2606.16671v2».TwoTerm.local_unique`
(Local coefficient uniqueness (C.1), requiring only the three scalar prefixes).
Proof chain: `«2606.16671v2».TwoTerm.local_unique` — 2606.16671v2, Theorem C.1; Local uniqueness of
the causal two-term realization.
Source: mathlib polynomial theory; NIST Digital Library of Mathematical Functions, Chapter 18 —
Chebyshev degree and affine polynomial substitution. The needed form is proved here.
-/
namespace «2606.16671v2».SpectralInterval
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Polynomial
variable (I : SpectralInterval)

/--
Equality on the nondegenerate spectral interval is polynomial equality.

Exact identity `p = q`.

Use: `«2606.16671v2».Stepsize.final_polynomial_eq` uses this identity to establish exact
identity `polynomial gamma N = I.residual N`.

Article: 2606.16671v2, Theorem C.1 via `«2606.16671v2».TwoTerm.local_unique`.

Source: mathlib polynomial theory; NIST Digital Library of Mathematical Functions, Chapter 18 —
Chebyshev degree and affine polynomial substitution.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem polynomial_eq {p q : ℝ[X]}
    (h : ∀ lam ∈ Set.Icc I.mu I.L, p.eval lam = q.eval lam) : p = q :=
  p.eq_of_infinite_eval_eq q ((Set.Icc_infinite I.mu_lt_L).mono h)

/--
Exact identity `(I.residual n).natDegree = n`.

Use: `«2606.16671v2».TwoTerm.local_unique` uses this identity to establish the identity `a =
1 + Prefix.beta I (n + 1) ∧ b = -Prefix.beta I (n + 1) ∧ g = Prefix.gamma I (n + 1)`.

Article: 2606.16671v2, Theorem C.1 via `«2606.16671v2».TwoTerm.local_unique`.

Source: mathlib polynomial theory; NIST Digital Library of Mathematical Functions, Chapter 18 —
Chebyshev degree and affine polynomial substitution.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.delta_pos`,
`«2606.16671v2».SpectralInterval.den_ne` with the arguments shown in the proof.
-/
theorem residual_natDegree (n : ℕ) : (I.residual n).natDegree = n := by
  have ha : (2 / I.delta : ℝ) ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt I.delta_pos)
  have hz : (Polynomial.C I.eta - Polynomial.C (2 / I.delta) * X).natDegree = 1 := by
    rw [← neg_sub, natDegree_neg,
      natDegree_sub_C, natDegree_C_mul_X _ ha]
  rw [residual, natDegree_C_mul (inv_ne_zero (I.den_ne n)), natDegree_comp, hz]
  simp

/--
The precise assertion is `I.residual n ≠ 0`.

Use: `«2606.16671v2».TwoTerm.local_unique` uses this assertion to establish the identity `a =
1 + Prefix.beta I (n + 1) ∧ b = -Prefix.beta I (n + 1) ∧ g = Prefix.gamma I (n + 1)`.

Article: 2606.16671v2, Theorem C.1 via `«2606.16671v2».TwoTerm.local_unique`.

Source: mathlib polynomial theory; NIST Digital Library of Mathematical Functions, Chapter 18 —
Chebyshev degree and affine polynomial substitution.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.residual_eval`,
`«2606.16671v2».SpectralInterval.den_ne`, `«2606.16671v2».SpectralInterval.z_mu` with the
arguments shown in the proof.
-/
theorem residual_ne_zero (n : ℕ) : I.residual n ≠ 0 := by
  intro h
  have he := I.residual_eval n I.mu
  rw [h, Polynomial.eval_zero, I.z_mu, T_eval_one] at he
  exact (one_div_ne_zero (I.den_ne n)) he.symm

end
end «2606.16671v2».SpectralInterval
