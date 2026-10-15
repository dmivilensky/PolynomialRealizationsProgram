import «2606.16671v2».SineJacobi.BinomialRatio
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
Article: 2606.16671v2, Theorem E.3.
Binomial Convolution.
Use: `«2606.16671v2».SineJacobi.binomialRatio_convolution` feeds
`«2606.16671v2».SineJacobi.endpoint_half_bound` (endpoint half bound).
Proof chain: `«2606.16671v2».SineJacobi.endpoint_global_bound` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Data.Nat.Choose.Vandermonde — generalized Vandermonde convolution. The
needed form is proved here.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open scoped BigOperators

/--
Exact identity `((n:ℝ)+1)*Ring.choose r (n+1) = Ring.choose r n*(r-(n:ℝ))`.

Use: `«2606.16671v2».SineJacobi.choose_neg_half` rewrites with this identity to establish exact
identity `Ring.choose (-1/2:ℝ) n = (-1:ℝ)^n * binomialRatio n`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Data.Nat.Choose.Vandermonde — generalized Vandermonde convolution.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem real_choose_recurrence (r : ℝ) (n : ℕ) :
    ((n:ℝ)+1)*Ring.choose r (n+1) = Ring.choose r n*(r-(n:ℝ)) := by
  have hb := Ring.choose_smul_choose r (n := n+1) (k := n) (Nat.le_succ n)
  simpa [nsmul_eq_mul] using hb

/--
Exact identity `Ring.choose (-1/2:ℝ) n = (-1:ℝ)^n * binomialRatio n`.

Use: `«2606.16671v2».SineJacobi.binomialRatio_convolution_antidiagonal` rewrites with this
identity to establish the identity `∑ ij ∈ Finset.antidiagonal n, binomialRatio
ij.1*binomialRatio ij.2 = 1`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Data.Nat.Choose.Vandermonde — generalized Vandermonde convolution.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Clear the
denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem choose_neg_half (n : ℕ) :
    Ring.choose (-1/2:ℝ) n = (-1:ℝ)^n * binomialRatio n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp
  | succ n ih =>
    apply mul_left_cancel₀ (show (n:ℝ)+1 ≠ 0 by positivity)
    rw [real_choose_recurrence, ih, binomialRatio, pow_succ]
    field_simp
    ring

/--
Exact identity `∑ ij ∈ Finset.antidiagonal n, binomialRatio ij.1*binomialRatio ij.2 = 1`.

Use: `«2606.16671v2».SineJacobi.binomialRatio_convolution` uses this identity to establish
exact identity `∑ k ∈ Finset.range (n+1), binomialRatio k*binomialRatio (n-k) = 1`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Data.Nat.Choose.Vandermonde — generalized Vandermonde convolution.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem binomialRatio_convolution_antidiagonal (n : ℕ) :
    ∑ ij ∈ Finset.antidiagonal n, binomialRatio ij.1*binomialRatio ij.2 = 1 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hb := Ring.add_choose_eq n (Commute.all (-1/2:ℝ) (-1/2:ℝ))
  have hl : Ring.choose (-1/2 + -1/2:ℝ) n = (-1:ℝ)^n := by
    norm_num only [show (-1/2 + -1/2:ℝ) = -1 by norm_num]
    rw [show (-1:ℝ) = -(1:ℝ) by ring, Ring.choose_neg']
    simp [Units.smul_def, zsmul_eq_mul]
  rw [hl] at hb
  have hsum : (∑ ij ∈ Finset.antidiagonal n,
      Ring.choose (-1/2:ℝ) ij.1 * Ring.choose (-1/2:ℝ) ij.2) =
      (-1:ℝ)^n * (∑ ij ∈ Finset.antidiagonal n,
        binomialRatio ij.1*binomialRatio ij.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [choose_neg_half, choose_neg_half]
    have hn := Finset.mem_antidiagonal.mp hij
    rw [show (-1:ℝ)^ij.1*binomialRatio ij.1*((-1:ℝ)^ij.2*binomialRatio ij.2) =
      ((-1:ℝ)^ij.1*(-1:ℝ)^ij.2)*(binomialRatio ij.1*binomialRatio ij.2) by ring,
      ← pow_add, hn]
  rw [hsum] at hb
  exact (mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1:ℝ) ≠ 0)))
    (by simpa using hb.symm)

/--
Exact identity `∑ k ∈ Finset.range (n+1), binomialRatio k*binomialRatio (n-k) = 1`.

Use: `«2606.16671v2».SineJacobi.endpoint_half_bound` rewrites with this identity to establish
the stated quantitative bound `endpoint N s ≤ (Real.pi^2/2)*Real.sqrt ((s:ℝ)+1)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpoint_global_bound`.

Source: mathlib, Mathlib.Data.Nat.Choose.Vandermonde — generalized Vandermonde convolution.

Proof: Use the identities/estimates
`«2606.16671v2».SineJacobi.binomialRatio_convolution_antidiagonal` with the arguments shown in
the proof.
-/
theorem binomialRatio_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), binomialRatio k*binomialRatio (n-k) = 1 := by
  have hb := binomialRatio_convolution_antidiagonal n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => binomialRatio i*binomialRatio j) n] at hb
  exact hb

end
end «2606.16671v2».SineJacobi
