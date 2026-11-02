import bezout.Channel.Roots.Energy

/-!
Article: bezout, Proposition D.1, finite interior modes are lower order.
Use: an explicit constant at each strict interior chart point bounds the actual
root-step profile by (2 epsilon/Delta)^2 C(x) N^2, uniformly in the horizon.
Proof: the sine formula for U bounds the weighted first derivative; the exact
Chebyshev differential equation bounds the weighted second derivative.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- Explicit finite bulk constant at a strict interior Chebyshev coordinate. -/
def interiorConstant (x : ℝ) : ℝ := (2+1/Real.sqrt (1-x^2))/(1-x^2)

/-- A strict interior point has a positive squared sine. -/
theorem interior_sine_pos {x : ℝ} (hx : |x|<1) : 0<1-x^2 := by
  have h := abs_lt.mp hx
  nlinarith

/-- The trigonometric second-kind formula gives a degree-independent weighted bound. -/
theorem abs_U_interior_mul_sine (n : ℤ) {x : ℝ} (hx : |x|<1) :
    |(U ℝ n).eval x| *Real.sqrt (1-x^2)≤1 := by
  have h := U_real_cos (n := n) (θ := Real.arccos x)
  rw [Real.cos_arccos (abs_le.mp hx.le).1 (abs_le.mp hx.le).2,Real.sin_arccos] at h
  have ha := congrArg abs h
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at ha
  exact ha.trans_le (Real.abs_sin_le_one _)

/-- The weighted first derivative is bounded by the exact horizon. -/
theorem abs_T_derivative_interior_mul_sine (N : ℕ) {x : ℝ} (hx : |x|<1) :
    |(T ℝ N).derivative.eval x| *Real.sqrt (1-x^2)≤N := by
  have he : (T ℝ N).derivative.eval x=(N:ℝ)*(U ℝ ((N:ℤ)-1)).eval x := by
    rw [T_derivative_eq_U]
    simp
  rw [he,abs_mul,abs_of_nonneg (Nat.cast_nonneg N),mul_assoc]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (abs_U_interior_mul_sine ((N:ℤ)-1) hx) (Nat.cast_nonneg N)

/-- A natural horizon is bounded by its square. -/
theorem horizon_le_square (N : ℕ) : (N:ℝ)≤(N:ℝ)^2 := by
  by_cases hN : N=0
  · simp [hN]
  · have h : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
    nlinarith

/-- The logarithmic-derivative energy of T_N has only quadratic growth at fixed interior x. -/
theorem chebyshev_interior_energy_le (N : ℕ) {x : ℝ} (hx : |x|<1) :
    (T ℝ N).derivative.eval x ^ 2 - (T ℝ N).eval x*(T ℝ N).derivative.derivative.eval x ≤
      interiorConstant x*(N:ℝ)^2 := by
  have hd := interior_sine_pos hx
  have hw : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr hd
  have hT := abs_eval_T_real_le_one (N:ℤ) hx.le
  have hD := abs_T_derivative_interior_mul_sine N hx
  have hD' : |(T ℝ N).derivative.eval x|≤(N:ℝ)/Real.sqrt (1-x^2) :=
    (le_div_iff₀ hw).mpr hD
  have hsq := (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hw.le) (Nat.cast_nonneg N)).mpr hD
  rw [mul_pow,sq_abs,Real.sq_sqrt hd.le] at hsq
  have hODE := congrArg (fun p : ℝ[X] => p.eval x)
    (one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℝ) (N:ℤ))
  simp only [eval_mul,eval_sub,eval_one,eval_pow,eval_X,eval_intCast,
    Function.iterate_succ_apply',Function.iterate_zero_apply] at hODE
  push_cast at hODE
  have hDD : |(1-x^2)*(T ℝ N).derivative.derivative.eval x|≤
      (N:ℝ)/Real.sqrt (1-x^2)+(N:ℝ)^2 := by
    rw [hODE]
    calc
      _ ≤ |x*(T ℝ N).derivative.eval x| +|(N:ℝ)^2*(T ℝ N).eval x| := abs_sub _ _
      _ = |x| *|(T ℝ N).derivative.eval x| +(N:ℝ)^2*|(T ℝ N).eval x| := by
        simp only [abs_mul,abs_of_nonneg (sq_nonneg (N:ℝ))]
      _ ≤ 1*((N:ℝ)/Real.sqrt (1-x^2))+(N:ℝ)^2*1 :=
        add_le_add (mul_le_mul hx.le hD' (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hT (sq_nonneg _))
      _ = _ := by ring
  have hP : -(T ℝ N).eval x*((1-x^2)*(T ℝ N).derivative.derivative.eval x)≤
      (N:ℝ)/Real.sqrt (1-x^2)+(N:ℝ)^2 := by
    calc
      _ ≤ |(T ℝ N).eval x*((1-x^2)*(T ℝ N).derivative.derivative.eval x)| := by
        simpa only [neg_mul] using neg_le_abs ((T ℝ N).eval x*((1-x^2)*(T ℝ N).derivative.derivative.eval x))
      _ = |(T ℝ N).eval x| *|(1-x^2)*(T ℝ N).derivative.derivative.eval x| := abs_mul _ _
      _ ≤ 1*((N:ℝ)/Real.sqrt (1-x^2)+(N:ℝ)^2) := mul_le_mul hT hDD (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hNN := div_le_div_of_nonneg_right (horizon_le_square N) hw.le
  have he : interiorConstant x*(N:ℝ)^2=((2+1/Real.sqrt (1-x^2))*(N:ℝ)^2)/(1-x^2) := by
    unfold interiorConstant
    ring
  rw [he]
  apply (le_div_iff₀ hd).mpr
  simp only [div_eq_mul_inv,one_mul] at hP hNN ⊢
  nlinarith

/-- Exact physical scaling of the root-profile derivative energy. -/
theorem residual_energy_scale (I : chebyshev1.SpectralInterval) (N : ℕ) (lam : ℝ) :
    (I.residual N).derivative.eval lam ^ 2 -
      (I.residual N).eval lam*(I.residual N).derivative.derivative.eval lam =
    (2*I.epsilon N/I.delta)^2 * ((T ℝ N).derivative.eval (I.z lam)^2 -
      (T ℝ N).eval (I.z lam)*(T ℝ N).derivative.derivative.eval (I.z lam)) := by
  simp [chebyshev1.SpectralInterval.residual,derivative_comp,derivative_mul,
    ← I.z_eq,chebyshev1.SpectralInterval.epsilon]
  ring

/-- Fixed interior spectral modes contribute only quadratic root-step energy. -/
theorem diagonalEnergy_interior_le (γ : ℕ → ℝ) (I : chebyshev1.SpectralInterval)
    (N : ℕ) (he : chebyshev1.Stepsize.FinalExact γ I N) {lam : ℝ}
    (hlam : |I.z lam|<1) :
    crossEnergy γ N lam lam≤(2*I.epsilon N/I.delta)^2*interiorConstant (I.z lam)*(N:ℝ)^2 := by
  rw [diagonalEnergy_derivatives,chebyshev1.Stepsize.final_polynomial_eq γ I N he,
    residual_energy_scale]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (chebyshev_interior_energy_le N hlam) (sq_nonneg (2*I.epsilon N/I.delta))

end
end bezout.Channel.Roots
