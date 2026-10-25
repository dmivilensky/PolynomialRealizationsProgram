import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

/-!
Article: chebyshev1, Remark 5.5.
Binary recursion for the consecutive pair `(T_n(x), T_{n+1}(x))`.
Use: `chebyshev1.chebyshevPair_real` feeds
`chebyshev1.amplification_certificate_five_percent` (amplification certificate five percent).
Proof chain: `chebyshev1.terminal_certificate` — chebyshev1, Remark 5.5; Exact drift scale,
accuracy asymptotics and rational finite examples.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev three-term
recurrence. The needed form is proved here.
-/
namespace chebyshev1
open Polynomial Polynomial.Chebyshev

/--
Binary recursion for the consecutive pair `(T_n(x), T_{n+1}(x))`. The rational arithmetic is
exact and all certificates are checked by the kernel.

Use: `chebyshev1.chebyshevPair_correct` rewrites with this definition to establish exact
identity `chebyshevPair x n = ((T ℚ n).eval x, (T ℚ (n+1:ℕ)).eval x)`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.terminal_certificate`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev three-term
recurrence.
-/
def chebyshevPair (x : ℚ) (n : ℕ) : ℚ × ℚ :=
  if hn : n = 0 then (1,x) else
    let p := chebyshevPair x (n/2)
    if n%2 = 0 then (2*p.1^2-1, 2*p.1*p.2-x)
    else (2*p.1*p.2-x, 2*p.2^2-1)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num)

/--
Exact identity `(T ℚ (2*n:ℕ)).eval x = 2*((T ℚ n).eval x)^2-1`.

Use: `chebyshev1.chebyshevPair_correct` uses this identity to establish the identity
`chebyshevPair x n = ((T ℚ n).eval x, (T ℚ (n+1:ℕ)).eval x)`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.terminal_certificate`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev three-term
recurrence.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem eval_double (x : ℚ) (n : ℕ) :
    (T ℚ (2*n:ℕ)).eval x = 2*((T ℚ n).eval x)^2-1 := by
  have h := congrArg (fun p : ℚ[X] => p.eval x) (T_mul_T ℚ n n)
  simp only [eval_mul, eval_ofNat, eval_add, sub_self, T_zero, eval_one] at h
  have hi : (n:ℤ)+n = (2*n:ℕ) := by push_cast; ring
  rw [hi] at h
  nlinarith

/--
Exact identity `(T ℚ (2*n+1:ℕ)).eval x = 2*(T ℚ n).eval x*(T ℚ (n+1:ℕ)).eval x-x`.

Use: `chebyshev1.chebyshevPair_correct` uses this identity to establish the identity
`chebyshevPair x n = ((T ℚ n).eval x, (T ℚ (n+1:ℕ)).eval x)`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.terminal_certificate`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev three-term
recurrence.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem eval_double_add_one (x : ℚ) (n : ℕ) :
    (T ℚ (2*n+1:ℕ)).eval x = 2*(T ℚ n).eval x*(T ℚ (n+1:ℕ)).eval x-x := by
  have h := congrArg (fun p : ℚ[X] => p.eval x) (T_mul_T ℚ n (n+1:ℕ))
  have hi : (n:ℤ)+(n+1:ℕ) = (2*n+1:ℕ) := by push_cast; ring
  have hj : (n:ℤ)-(n+1:ℕ) = -1 := by push_cast; ring
  simp only [eval_mul, eval_ofNat, eval_add, hi, hj, T_neg_one, eval_X] at h
  linarith

/--
Exact identity `chebyshevPair x n = ((T ℚ n).eval x, (T ℚ (n+1:ℕ)).eval x)`.

Use: `chebyshev1.chebyshevPair_real` rewrites with this identity to establish exact
identity `((chebyshevPair x n).1:ℝ) = (T ℝ n).eval (x:ℝ)`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.terminal_certificate`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev three-term
recurrence.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem chebyshevPair_correct (x : ℚ) (n : ℕ) :
    chebyshevPair x n = ((T ℚ n).eval x, (T ℚ (n+1:ℕ)).eval x) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [chebyshevPair]
    split_ifs with hn hp
    · subst n; simp
    · rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))]
      have he : n = 2*(n/2) := by omega
      apply Prod.ext
      · change _ = (T ℚ n).eval x
        simpa only [← he] using (eval_double x (n/2)).symm
      · change _ = (T ℚ (n+1:ℕ)).eval x
        simpa only [← he] using (eval_double_add_one x (n/2)).symm
    · rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))]
      have he : n = 2*(n/2)+1 := by omega
      have hj : n+1 = 2*(n/2+1) := by omega
      apply Prod.ext
      · change _ = (T ℚ n).eval x
        simpa only [← he] using (eval_double_add_one x (n/2)).symm
      · change _ = (T ℚ (n+1:ℕ)).eval x
        simpa only [← hj] using (eval_double x (n/2+1)).symm

/--
Exact identity `((chebyshevPair x n).1:ℝ) = (T ℝ n).eval (x:ℝ)`.

Use: `chebyshev1.amplification_certificate_five_percent` rewrites with this identity to
establish the stated quantitative bound `(128/10:ℝ) < (T ℝ (725:ℕ)).eval (1+2*(1/20)/9999) ∧ (T
ℝ (725:ℕ)).eval (1+2*(1/20)/9999) < (129/10:ℝ)`.

Article: chebyshev1, Remark 5.5 via `chebyshev1.terminal_certificate`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev three-term
recurrence.

Proof: Use the identities/estimates `chebyshev1.chebyshevPair_correct` with the arguments
shown in the proof.
-/
theorem chebyshevPair_real (x : ℚ) (n : ℕ) :
    ((chebyshevPair x n).1:ℝ) = (T ℝ n).eval (x:ℝ) := by
  rw [chebyshevPair_correct]
  exact algebraMap_eval_T x n

end chebyshev1
