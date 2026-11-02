import krylov.Envelope.HeavyBallPolynomial
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), genuine heavy-ball continuation endpoint maximum.
Use: prove the actual Chebyshev-U continuation bound and its exact right-endpoint attainment.
Source: reuse the earlier proved Chebyshev-U interval bound and mathlib genuine endpoint evaluations with their real alternating signs.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Polynomial.Chebyshev chebyshev1

/-- The actual constant-coefficient continuation has the printed sharp heavy-ball interval upper bound.
Use: The actual constant-coefficient continuation has the printed sharp heavy-ball interval upper bound.
Article: main_krylov, prop:phi(b), genuine heavy-ball continuation endpoint maximum.
Proof: Apply the genuine Chebyshev-U formula and the earlier actual bounds for both true adjacent degrees, treating the empty suffix separately. -/
theorem constant_phi_abs_bound (α q : ℝ) (hα : α≠0) (hq : 0 < q) (j k : ℕ) (lam : ℝ)
    (hz : |(1+q^2-α*lam)/(2*q)|≤1) :
    |(phi (fun _ => α) (fun _ => q^2) j k).eval lam|≤q^k*((k:ℝ)+1+q*k) := by
  -- Bound the two actual adjacent Chebyshev degrees without replacing the degree-zero boundary.
  rw [constant_phi_chebyshev α q hα hq.ne']
  rw [abs_mul,abs_of_nonneg (pow_nonneg hq.le k)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq.le k)
  cases k with
  | zero => simp [U_neg_one]
  -- The genuine two endpoint parities supply exactly the printed relative addition of magnitudes.
  | succ k =>
    have h0 := abs_U_eval_le (k+1) hz
    have h1 := abs_U_eval_le k hz
    have hi : ((k+1:ℕ):ℤ)-1=(k:ℤ) := by omega
    rw [hi]
    calc
      _ ≤ |(U ℝ ((k+1:ℕ):ℤ)).eval ((1+q^2-α*lam)/(2*q))|+
          |q*(U ℝ (k:ℤ)).eval ((1+q^2-α*lam)/(2*q))| := abs_sub _ _
      _ ≤ ((k+1:ℕ):ℝ)+1+q*((k:ℝ)+1) := by
        rw [abs_mul,abs_of_pos hq]
        exact add_le_add h0 (mul_le_mul_of_nonneg_left h1 hq.le)
      _ = _ := by push_cast;ring

/-- The actual continuation has the genuine alternating printed value at the right spectral endpoint.
Use: The actual continuation has the genuine alternating printed value at the right spectral endpoint.
Article: main_krylov, prop:phi(b), genuine heavy-ball continuation endpoint maximum.
Proof: Evaluate both true Chebyshev polynomials at minus one and retain their actual relative parity. -/
theorem constant_phi_at_right (α q : ℝ) (hα : α≠0) (hq : q≠0) (j k : ℕ) (L : ℝ)
    (hL : (1+q^2-α*L)/(2*q)= -1) :
    (phi (fun _ => α) (fun _ => q^2) j k).eval L=
      (-q)^k*((k:ℝ)+1+q*k) := by
  -- Keep the genuine integer Chebyshev endpoint parities until both adjacent degrees have been evaluated.
  rw [constant_phi_chebyshev α q hα hq j k L,hL]
  cases k with
  | zero => simp [U_neg_one]
  | succ k =>
    have hi : ((k+1:ℕ):ℤ)-1=(k:ℤ) := by omega
    rw [hi,U_eval_neg_one,U_eval_neg_one]
    simp only [Int.cast_negOnePow,zpow_natCast,Int.cast_natCast]
    rw [neg_pow q (k+1)]
    push_cast
    simp only [pow_succ]
    ring

/-- The actual absolute continuation attains the printed positive heavy-ball constant at the right endpoint.
Use: The actual absolute continuation attains the printed positive heavy-ball constant at the right endpoint.
Article: main_krylov, prop:phi(b), genuine heavy-ball continuation endpoint maximum.
Proof: Take the genuine absolute value of its true alternating endpoint formula. -/
theorem constant_phi_abs_at_right (α q : ℝ) (hα : α≠0) (hq : 0 < q) (j k : ℕ) (L : ℝ)
    (hL : (1+q^2-α*L)/(2*q)= -1) :
    |(phi (fun _ => α) (fun _ => q^2) j k).eval L|=q^k*((k:ℝ)+1+q*k) := by
  rw [constant_phi_at_right α q hα hq.ne' j k L hL,abs_mul,abs_pow,abs_neg,
    abs_of_pos hq,abs_of_nonneg (by positivity)]
end
end krylov.Envelope
