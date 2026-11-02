import bezout.Flat.History

/-!
Article: bezout, Algorithm 1, scalar preparation and virtual-state verification.
Use: exact recurrence coefficients for the physical four-vector implementation.
Proof: substitute the affine spectral coordinate into the normalized U
recurrence; the final first-kind identity gives the prescribed terminal.
-/

namespace bezout.Flat
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The virtual-state residual in physical spectral coordinates.
Use: the error-free vectors V and P maintained by Flat. -/
def virtualPolynomial (I : chebyshev1.SpectralInterval) (s : ℕ) : ℝ[X] :=
  (normalizedU I s).comp (C I.eta - C (2 / I.delta) * X)

/-- Physical evaluation of a virtual state.
Use: scalar proofs of the exact in-place recurrence. -/
theorem virtualPolynomial_eval (I : chebyshev1.SpectralInterval) (s : ℕ) (lam : ℝ) :
    (virtualPolynomial I s).eval lam = (U ℝ s).eval (I.z lam) / u I s := by
  simp only [virtualPolynomial, eval_comp, normalizedU, eval_mul, eval_C, eval_sub, eval_X]
  rw [← I.z_eq]
  ring

/-- The Flat virtual stepsize, including its separately prescribed startup.
Use: Algorithm 1's scalar preparation. -/
def alpha (I : chebyshev1.SpectralInterval) (s : ℕ) : ℝ :=
  if s = 0 then 2 / (I.L + I.mu) else 4 * u I s / (I.delta * u I (s + 1))

/-- The Flat virtual momentum, including zero startup momentum.
Use: Algorithm 1's scalar preparation. -/
def beta (I : chebyshev1.SpectralInterval) (s : ℕ) : ℝ :=
  if s = 0 then 0 else u I (s - 1) / u I (s + 1)

/-- Initial virtual state.
Use: both physical state registers start at the initial error. -/
@[simp] theorem virtualPolynomial_zero (I : chebyshev1.SpectralInterval) :
    virtualPolynomial I 0 = 1 := by simp [virtualPolynomial]

/-- The initial normalized U step has exactly the prescribed stepsize.
Use: startup of the physical iteration. -/
theorem virtualPolynomial_one (I : chebyshev1.SpectralInterval) :
    virtualPolynomial I 1 = 1 - C (alpha I 0) * X := by
  apply Polynomial.funext
  intro lam
  rw [virtualPolynomial_eval]
  simp only [Nat.cast_one, U_one, eval_mul, eval_ofNat, eval_X, u_one, eval_sub, eval_one, eval_C, alpha, ite_true]
  rw [I.z_eq]
  have hd := ne_of_gt I.delta_pos
  have hsum : I.L + I.mu ≠ 0 := ne_of_gt (by linarith [I.mu_pos, I.mu_lt_L])
  unfold chebyshev1.SpectralInterval.eta
  field_simp [hd, hsum]

/-- The exact normalized U recurrence after physical coordinate substitution.
Use: every nonterminal virtual step of the four-vector implementation. -/
theorem virtualPolynomial_step (I : chebyshev1.SpectralInterval) (s : ℕ) :
    virtualPolynomial I (s + 2) =
      C (1 + beta I (s + 1)) * virtualPolynomial I (s + 1) -
      C (beta I (s + 1)) * virtualPolynomial I s -
      C (alpha I (s + 1)) * X * virtualPolynomial I (s + 1) := by
  apply Polynomial.funext
  intro lam
  simp only [eval_sub, eval_mul, eval_C, eval_X, virtualPolynomial_eval]
  have hr := congrArg (fun p : ℝ[X] => p.eval (I.z lam)) (U_add_two ℝ (s : ℤ))
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hr
  have hu := u_add_two I s
  simp only [alpha, beta, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [hr]
  generalize hv1 : (U ℝ ((s : ℤ) + 1)).eval (I.z lam) = v1
  generalize hv0 : (U ℝ s).eval (I.z lam) = v0
  rw [I.z_eq]
  have hd := ne_of_gt I.delta_pos
  have h0 := ne_of_gt (u_pos I s)
  have h1 := ne_of_gt (u_pos I (s + 1))
  have h2 := ne_of_gt (u_pos I (s + 2))
  simp only [show s + 1 + 1 = s + 2 by omega]
  field_simp [hd, h0, h1, h2]
  linear_combination -v1 * I.delta * hu

/-- The terminal momentum coefficient in Algorithm 1.
Use: the final first-kind extraction from the second-kind virtual states. -/
def terminalA (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  u I (N - 2) / I.den N

/-- The terminal gradient coefficient in Algorithm 1.
Use: the final physical oracle answer is used once. -/
def terminalB (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  2 * u I (N - 1) / (I.delta * I.den N)

/-- The final virtual step has precisely the prescribed normalized Chebyshev terminal.
Use: identifies the literal Flat algorithm with its synthesized exact history. -/
theorem virtualPolynomial_terminal (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    I.residual N =
      C (1 + terminalA I N) * virtualPolynomial I (N - 1) -
      C (terminalA I N) * virtualPolynomial I (N - 2) -
      C (terminalB I N) * X * virtualPolynomial I (N - 1) := by
  apply Polynomial.funext
  intro lam
  rw [I.residual_eval]
  simp only [eval_sub, eval_mul, eval_C, eval_X, virtualPolynomial_eval, terminalA, terminalB]
  have hi : ((N - 2 : ℕ) : ℤ) + 2 = (N : ℤ) := by omega
  have him : ((N - 2 : ℕ) : ℤ) + 1 = ((N - 1 : ℕ) : ℤ) := by omega
  have hr := congrArg (fun p : ℝ[X] => p.eval (I.z lam))
    (T_eq_X_mul_U_sub_U ℝ ((N - 2 : ℕ) : ℤ))
  simp only [eval_sub, eval_mul, eval_X] at hr
  rw [him, hi] at hr
  have hd := ne_of_gt I.delta_pos
  have h0 := ne_of_gt (u_pos I (N - 2))
  have h1 := ne_of_gt (u_pos I (N - 1))
  have hC := I.den_ne N
  have hc := congrArg (fun p : ℝ[X] => p.eval I.eta)
    (T_eq_X_mul_U_sub_U ℝ ((N - 2 : ℕ) : ℤ))
  simp only [eval_sub, eval_mul, eval_X] at hc
  rw [him, hi] at hc
  change I.den N = I.eta * u I (N - 1) - u I (N - 2) at hc
  rw [hr]
  generalize hv1 : (U ℝ ((N - 1 : ℕ) : ℤ)).eval (I.z lam) = v1
  generalize hv0 : (U ℝ ((N - 2 : ℕ) : ℤ)).eval (I.z lam) = v0
  rw [I.z_eq]
  field_simp [hd, h0, h1, hC]
  linear_combination -v1 * I.delta * hc

end
end bezout.Flat
