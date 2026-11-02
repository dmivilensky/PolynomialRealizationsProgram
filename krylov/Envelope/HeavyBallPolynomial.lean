import krylov.Envelope.ContinuationSecondOrder
import chebyshev1.Chebyshev.Normalization
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), true constant-coefficient heavy-ball continuation.
Use: identify the actual continuation polynomial from its genuine constant line and momentum coefficients, including the empty suffix.
Source: the original measured continuation recurrence and mathlib genuine integer-indexed Chebyshev polynomials of the second kind, with U at minus one equal to zero.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The actual constant-coefficient CG continuation has the printed genuine Chebyshev-U formula, including degree zero.
Use: The actual constant-coefficient CG continuation has the printed genuine Chebyshev-U formula, including degree zero.
Article: main_krylov, prop:phi(b), true constant-coefficient heavy-ball continuation.
Proof: Match the true initial two continuations and use the genuine three-term recurrence together with the actual Chebyshev recurrence and its affine coordinate. -/
theorem constant_phi_chebyshev (α q : ℝ) (hα : α≠0) (hq : q≠0) (j k : ℕ) (lam : ℝ) :
    (phi (fun _ => α) (fun _ => q^2) j k).eval lam=
      q^k*((U ℝ (k:ℤ)).eval ((1+q^2-α*lam)/(2*q))-
        q*(U ℝ ((k:ℤ)-1)).eval ((1+q^2-α*lam)/(2*q))) := by
  -- The actual affine coordinate preserves the genuine heavy-ball recurrence coefficient exactly.
  let z := (1+q^2-α*lam)/(2*q)
  have hz : 2*q*z=1+q^2-α*lam := by
    dsimp only [z]
    field_simp
  induction k using Nat.twoStepInduction with
  | zero => simp [U_neg_one,phi_zero]
  | one =>
    rw [phi_one]
    simp only [eval_sub,eval_one,eval_mul,eval_C,eval_X,pow_one,Nat.cast_one,
      Int.reduceSub,U_one,U_zero,eval_ofNat,mul_one]
    change 1-α*lam=q*(2*z-q)
    nlinarith [hz]
  -- Two genuine Chebyshev recurrences close the actual continuation induction without a terminal-beta premise.
  | more k ih0 ih1 =>
    rw [phi_add_two (fun _ => α) (fun _ => q^2) j k hα]
    simp only [eval_sub,eval_mul,eval_add,eval_one,eval_C,eval_X,mul_div_cancel_left₀ _ hα,ih0,ih1]
    have hU := congrArg (fun p : ℝ[X] => p.eval z) (U_add_two ℝ (k:ℤ))
    have hV := congrArg (fun p : ℝ[X] => p.eval z) (U_add_two ℝ ((k:ℤ)-1))
    simp only [eval_sub,eval_mul,eval_ofNat,eval_X] at hU hV
    have hi3 : (k:ℤ)-1+2=(k:ℤ)+1 := by omega
    have hi4 : (k:ℤ)-1+1=(k:ℤ) := by omega
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    rw [show (k:ℤ)+1-1=(k:ℤ) by omega,show (k:ℤ)+2-1=(k:ℤ)+1 by omega]
    rw [hi3,hi4] at hV
    change _=q^(k+2)*((U ℝ ((k:ℤ)+2)).eval z-q*(U ℝ ((k:ℤ)+1)).eval z)
    rw [hU]
    simp only [pow_add,pow_one]
    linear_combination -(q^k*q)*((U ℝ ((k:ℤ)+1)).eval z-q*(U ℝ (k:ℤ)).eval z)*hz+
      (q^k*q^3)*hV
end
end krylov.Envelope
