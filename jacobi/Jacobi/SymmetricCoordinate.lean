import jacobi.Jacobi.SymmetricRecurrence
import jacobi.Jacobi.QuadraticTransform

/-!
Article: jacobi, Proposition A.1.
The same original symmetric Jacobi polynomials are written in their
unshifted coordinate. Their proved degree recurrence gives the exact
coefficients of the original general-momentum Nesterov iteration.
Use: NesterovIdentification proves equality with the original recurrence.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original endpoint-normalized symmetric Jacobi polynomial in its true unshifted variable.
Use: NesterovIdentification connects its degree recurrence directly to the actual Nesterov error recurrence.
Article: jacobi, Proposition A.1.
-/
def symmetricUnit (a:ℝ) (n:ℕ) (z:ℝ) : ℝ := (shiftedPolynomial a a n).eval ((1-z)/2)

/-- The original shifted Jacobi polynomial of degree zero is literally the constant one polynomial.
Use: symmetricUnit_zero and symmetricUnit_one initialize the original residual identification in the actual polynomial ring.
Article: jacobi, Proposition A.1.
Proof: the terminating original hypergeometric sum contains only its unit zeroth coefficient. -/
@[simp] theorem shiftedPolynomial_degree_zero (a b:ℝ) : shiftedPolynomial a b 0=1 := by
  simp [shiftedPolynomial,coefficient,ordinaryHypergeometricCoefficient]

/-- The genuine zero-degree symmetric source polynomial is exactly one.
Use: initializes the actual original Nesterov residual identification.
Article: jacobi, Proposition A.1.
Proof: evaluate the original zero-degree shifted Jacobi polynomial. -/
@[simp] theorem symmetricUnit_zero (a z:ℝ) : symmetricUnit a 0 z=1 := by simp [symmetricUnit]

/-- The genuine first symmetric source polynomial is exactly the unshifted coordinate throughout the original positive-Gegenbauer-parameter range.
Use: initializes the second actual Nesterov error step with its original momentum coefficient zero.
Article: jacobi, Proposition A.1.
Proof: the actual zero-degree raising identity has nonzero coefficient 2*alpha+1. Cancel it to identify the first polynomial as 1-2*t, then use the exact unshifted coordinate. -/
@[simp] theorem symmetricUnit_one {a:ℝ} (ha:-(1/2:ℝ)<a) (z:ℝ) : symmetricUnit a 1 z=z := by
  -- This uses the proved original polynomial equation, rather than a separately defined degree-one polynomial.
  have hr:=symmetric_raise_eq (show -1<a by linarith) 0
  simp only [symmetricRaise,shiftedPolynomial_degree_zero,Nat.cast_zero,zero_add,derivative_one,mul_zero,add_zero,mul_one] at hr
  have hc:C (2*a+1)≠(0:Polynomial ℝ):=C_ne_zero.mpr (by linarith)
  have hp:=mul_left_cancel₀ hc hr
  dsimp [symmetricUnit]
  rw [hp]
  simp only [eval_sub,eval_one,eval_mul,eval_ofNat,eval_X]
  ring

/-- The actual unshifted symmetric Jacobi family obeys precisely the normalized Gegenbauer degree recurrence.
Use: NesterovIdentification applies it at alpha=b/2 and the same original iteration indices.
Article: jacobi, Proposition A.1.
Proof: evaluate the independently proved literal polynomial recurrence at t=(1-z)/2. The original affine factor 1-2*t becomes exactly z. -/
theorem symmetricUnit_recurrence {a:ℝ} (ha:-1<a) (n:ℕ) (z:ℝ) :
    ((n:ℝ)+2*a+2)*symmetricUnit a (n+2) z=
      (2*(n:ℝ)+2*a+3)*z*symmetricUnit a (n+1) z-((n:ℝ)+1)*symmetricUnit a n z := by
  have h:=congrArg (fun p:Polynomial ℝ=>p.eval ((1-z)/2)) (symmetric_degree_recurrence ha n)
  simp only [eval_mul,eval_C,eval_sub,eval_one,eval_ofNat,eval_X] at h
  dsimp only [symmetricUnit]
  convert h using 1; ring

/-- The original real symmetric source polynomial is exactly the normalized classical Gegenbauer function at each real argument.
Use: NesterovIdentification identifies the genuine original iteration with the literal Gegenbauer residual already used in the full hard-edge theorem.
Article: jacobi, Proposition A.1.
Proof: its complex evaluation is the previously proved original normalized Jacobi function. The already proved Gegenbauer specialization gives the same normalization, and the affine coordinate cancels exactly. -/
theorem symmetricUnit_gegenbauer {a:ℝ} (ha:-(1/2:ℝ)<a) (n:ℕ) (z:ℝ) :
    (symmetricUnit a n z:ℂ)=gegenbauer ((a+1/2:ℝ):ℂ) n (z:ℂ)/
      gegenbauer ((a+1/2:ℝ):ℂ) n 1 := by
  rw [gegenbauer_normalized (by simpa only [Complex.ofReal_re] using (show 0<a+1/2 by linarith))]
  have hp:((a+1/2:ℝ):ℂ)-1/2=(a:ℂ):=by push_cast; ring
  rw [hp]
  dsimp only [symmetricUnit]
  rw [shiftedPolynomial_eval,show 1-2*((1-z)/2)=z by ring]
  exact Complex.conj_eq_iff_re.mp (normalized_conj a a z n)

end
end jacobi.Jacobi
