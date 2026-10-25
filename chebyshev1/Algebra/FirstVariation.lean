import chebyshev1.Algebra.OrderedProduct
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
Article: chebyshev1, Lemma 1.1.
The first-order insertion sum is the actual derivative, not just a formal coefficient.
Use: `chebyshev1.hasDerivAt_orderedProduct_affine` feeds
`chebyshev1.Realization.hasDerivAt_operatorTransfer` (Lemma 1.1: the insertion sum is the actual
derivative at zero drift).
Proof chain: `chebyshev1.Realization.static_shift_lower_bounds_general` — chebyshev1, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
Source: mathlib, Mathlib.Analysis.Calculus.Deriv.Mul — Leibniz rule for a finite ordered product.
The needed form is proved here.
-/
namespace chebyshev1

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/--
Exact identity `orderedProduct (fun s => C s + (0 : ℝ) • D s) n = orderedProduct C n`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Lemma 1.1.

Source: mathlib, Mathlib.Analysis.Calculus.Deriv.Mul — Leibniz rule for a finite ordered
product.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
@[simp] theorem orderedProduct_affine_zero (C D : ℕ → A) (n : ℕ) :
    orderedProduct (fun s => C s + (0 : ℝ) • D s) n = orderedProduct C n := by simp

/--
The first-order insertion sum is the actual derivative, not just a formal coefficient.

The actual derivative at the stated point: `HasDerivAt (fun δ : ℝ => orderedProduct (fun s => C
s + δ • D s) n) (firstVariation C D n) 0`.

Use: `chebyshev1.deriv_orderedProduct_affine` uses this derivative formula to establish
exact identity `deriv (fun δ : ℝ => orderedProduct (fun s => C s + δ • D s) n) 0 =
firstVariation C D n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.Analysis.Calculus.Deriv.Mul — Leibniz rule for a finite ordered
product.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem hasDerivAt_orderedProduct_affine (C D : ℕ → A) (n : ℕ) :
    HasDerivAt (fun δ : ℝ => orderedProduct (fun s => C s + δ • D s) n)
      (firstVariation C D n) 0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simpa using (hasDerivAt_const (0 : ℝ) (1 : A))
  | succ n ih =>
    have hfactor : HasDerivAt (fun δ : ℝ => C n + δ • D n) (D n) 0 := by
      convert!
        ((hasDerivAt_id (0 : ℝ)).smul_const (D n)).const_add (C n)
        using 1
      simp
    convert! hfactor.mul ih using 1
    simp [firstVariation_succ]

/--
Exact identity `deriv (fun δ : ℝ => orderedProduct (fun s => C s + δ • D s) n) 0 =
firstVariation C D n`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Lemma 1.1.

Source: mathlib, Mathlib.Analysis.Calculus.Deriv.Mul — Leibniz rule for a finite ordered
product.

Proof: Use the identities/estimates `chebyshev1.hasDerivAt_orderedProduct_affine` with the
arguments shown in the proof.
-/
theorem deriv_orderedProduct_affine (C D : ℕ → A) (n : ℕ) :
    deriv (fun δ : ℝ => orderedProduct (fun s => C s + δ • D s) n) 0 =
      firstVariation C D n :=
  (hasDerivAt_orderedProduct_affine C D n).deriv

end chebyshev1
