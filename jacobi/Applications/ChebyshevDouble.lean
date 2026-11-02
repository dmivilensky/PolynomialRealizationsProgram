import jacobi.Applications.NesterovWave

/-!
Article: jacobi, Theorem 5.1.
The odd Chebyshev U polynomial has the literal quadratic transformation
needed to connect the original Nesterov recurrence to its actual U block.
Use: BlockTerminal identifies both original terminal transfers.
Source: the standard Chebyshev U recurrence, mathlib Polynomial.Chebyshev.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Polynomial.Chebyshev
set_option maxHeartbeats 1000000

/-- The two exact Chebyshev doubling identities, including the empty predecessor U_(-1)=0.
Use: nesterovWave_odd expresses the true original wave at every even application count without a Gegenbauer recurrence assumption.
Article: jacobi, Theorem 5.1.
Source: Chebyshev doubling formulas, proved from the community three-term recurrence.
Proof: carry the even and odd identities together. The even next index uses both old identities and the original U recurrence in the quadratic argument; the odd next index then follows from the same true recurrence. -/
theorem chebyshev_U_double (n:ℕ) :
    U ℝ (2*(n:ℤ)+1)=2*X*(U ℝ (n:ℤ)).comp (2*X^2-1) ∧
    U ℝ (2*(n:ℤ))=(U ℝ (n:ℤ)).comp (2*X^2-1)+
      (U ℝ ((n:ℤ)-1)).comp (2*X^2-1) := by
  -- The paired induction avoids division by X or by a sine, so both spectral endpoints are retained.
  induction n with
  | zero=>norm_num [U_one,U_zero,U_neg_one]
  | succ n ih=>
    have hq:=congrArg (fun p:Polynomial ℝ=>p.comp (2*X^2-1)) (U_add_one ℝ (n:ℤ))
    simp only [sub_comp,mul_comp,ofNat_comp,X_comp] at hq
    have he:U ℝ (2*(n:ℤ)+2)=(U ℝ ((n:ℤ)+1)).comp (2*X^2-1)+
        (U ℝ (n:ℤ)).comp (2*X^2-1):=by
      rw [U_add_two,ih.1,ih.2,hq]
      ring
    have ho:U ℝ (2*(n:ℤ)+3)=2*X*(U ℝ ((n:ℤ)+1)).comp (2*X^2-1):=by
      rw [show 2*(n:ℤ)+3=(2*(n:ℤ)+1)+2 by ring,U_add_two]
      rw [show 2*(n:ℤ)+1+1=2*(n:ℤ)+2 by ring,he,ih.1]
      ring
    push_cast
    constructor
    · simpa only [show 2*((n:ℤ)+1)+1=2*(n:ℤ)+3 by ring] using ho
    · simpa only [show 2*((n:ℤ)+1)=2*(n:ℤ)+2 by ring,add_sub_cancel_right] using he

/-- Every genuine odd original Nesterov wave is exactly the U-block factor with its integer Landweber power.
Use: BlockTerminal proves the actual original Nesterov and block transfers agree at every physical spectral value, including both endpoints.
Article: jacobi, Theorem 5.1.
Proof: substitute the true square-root wave formula into the exact Chebyshev quadratic identity. The two square-root factors combine into an integer power of 1-lambda. -/
theorem nesterovWave_odd (m:ℕ) {l:ℝ} (hl:l≤1) :
    nesterovWave (2*m+1) l=2*(1-l)^(m+1)*(U ℝ (m:ℤ)).eval (1-2*l) := by
  -- The exact polynomial identity also handles sqrt(1-lambda)=0 without cancellation.
  rw [nesterovWave_chebyshev _ hl]
  have hi:(2*m+1:ℕ)=2*(m:ℤ)+1:=by push_cast; ring
  rw [hi,(chebyshev_U_double m).1]
  simp only [eval_mul,eval_ofNat,eval_X,eval_comp,eval_sub,eval_pow,eval_one]
  have hs:(Real.sqrt (1-l))^2=1-l:=Real.sq_sqrt (by linarith)
  rw [hs,show 2*(1-l)-1=1-2*l by ring]
  rw [pow_add,pow_one]
  have hp:Real.sqrt (1-l)^(2*m)=(1-l)^m:=by
    rw [pow_mul,hs]
  rw [hp,pow_succ]
  linear_combination 2*(1-l)^m*(U ℝ (m:ℤ)).eval (1-2*l)*hs

end
end jacobi.Applications
