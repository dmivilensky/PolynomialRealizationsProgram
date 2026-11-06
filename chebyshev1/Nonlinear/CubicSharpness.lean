import chebyshev1.Nonlinear.WeightedSecondOrder
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The scalar cubic objective has the weighted second-order coefficient exactly.
All statements concern the actual finite recurrence. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Error polynomial for the scalar gradient `mu*x-rho*x^2/2`, with the initial
error represented by the indeterminate. -/
def cubicErrorPolynomial (S : TwoTerm) (mu rho : ℝ) : ℕ → ℝ[X]
  | 0 => X
  | 1 => X-C (S.gamma 0)*(C mu*X-C (rho/2)*X^2)
  | n+2 => C (S.a (n+1))*cubicErrorPolynomial S mu rho (n+1) +
      C (S.b (n+1))*cubicErrorPolynomial S mu rho n -
      C (S.gamma (n+1))*(C mu*cubicErrorPolynomial S mu rho (n+1)-
        C (rho/2)*(cubicErrorPolynomial S mu rho (n+1))^2)

theorem cubicErrorPolynomial_coeff_zero (S : TwoTerm) (mu rho : ℝ) (n : ℕ) :
    (cubicErrorPolynomial S mu rho n).coeff 0 = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cubicErrorPolynomial]
  | one => simp [cubicErrorPolynomial]
  | more n ih0 ih1 =>
    simp only [cubicErrorPolynomial, coeff_sub, coeff_add,
      pow_two, mul_coeff_zero, ih0, ih1, mul_zero, add_zero, sub_zero]

theorem square_coeff_one_of_constant_zero (P : ℝ[X]) (hP : P.coeff 0 = 0) :
    (P^2).coeff 1 = 0 := by simp [pow_two, mul_coeff_one, hP]

theorem square_coeff_two_of_constant_zero (P : ℝ[X]) (hP : P.coeff 0 = 0) :
    (P^2).coeff 2 = (P.coeff 1)^2 := by
  rw [pow_two, coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, hP, pow_two]

theorem cubicErrorPolynomial_coeff_one (S : TwoTerm) (mu rho : ℝ) (n : ℕ) :
    (cubicErrorPolynomial S mu rho n).coeff 1 =
      (S.realization.residualPolynomial n).eval mu := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cubicErrorPolynomial, S.residual_zero]
  | one => simp [cubicErrorPolynomial, S.residual_one, coeff_X_pow]
  | more n ih0 ih1 =>
    rw [cubicErrorPolynomial, S.residual_recurrence]
    simp only [coeff_sub, coeff_add, coeff_C_mul,
      square_coeff_one_of_constant_zero _ (cubicErrorPolynomial_coeff_zero S mu rho (n+1)),
      ih0, ih1, mul_zero, sub_zero, eval_add, eval_mul, eval_sub, eval_C, eval_X]
    ring

/-- Evaluation is precisely the scalar nonlinear recurrence in one coordinate. -/
theorem cubicErrorPolynomial_eval (S : TwoTerm) (mu rho r : ℝ) (n : ℕ) :
    (cubicErrorPolynomial S mu rho n).eval r =
      S.nonlinearError (fun v : Fin 1 → ℝ => fun i => mu*v i-rho/2*(v i)^2)
        (fun _ => r) n 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cubicErrorPolynomial, TwoTerm.nonlinearError]
  | one => simp [cubicErrorPolynomial, TwoTerm.nonlinearError]
  | more n ih0 ih1 =>
    simp [cubicErrorPolynomial, TwoTerm.nonlinearError, ih0, ih1]

theorem cubicErrorPolynomial_coeff_two_forced (S : TwoTerm) (mu rho : ℝ) (n : ℕ) :
    (cubicErrorPolynomial S mu rho n).coeff 2 =
      S.perturbedError (Matrix.diagonal (fun _ : Fin 1 => mu)) (fun _ => 0)
        (fun s _ => -(rho/2)*((S.realization.residualPolynomial s).eval mu)^2)
        (fun _ _ => 0) n 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cubicErrorPolynomial, TwoTerm.perturbedError, coeff_X]
  | one => simp [cubicErrorPolynomial, TwoTerm.perturbedError, S.residual_zero, coeff_X]
  | more n ih0 ih1 =>
    rw [cubicErrorPolynomial, TwoTerm.perturbedError]
    simp only [coeff_sub, coeff_add, coeff_C_mul,
      square_coeff_two_of_constant_zero _ (cubicErrorPolynomial_coeff_zero S mu rho (n+1)),
      cubicErrorPolynomial_coeff_one, ih0, ih1, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal, add_zero]
    ring

/-- The cubic scalar objective attains the endpoint-weighted second-order
coefficient exactly at every fixed horizon. -/
theorem cubicErrorPolynomial_coeff_two (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (rho : ℝ) :
    (cubicErrorPolynomial ((family.data N).method I) I.mu rho N).coeff 2 =
      (rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N := by
  let J := family.data N
  let H : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal (fun _ => I.mu)
  have ha := family.admissible I hN
  have hp (s : ℕ) (hs : s ≤ N) :
      ((J.method I).realization.residualPolynomial s).eval I.mu = leadingRadius J I s := by
    rw [show (J.method I).realization = J.realization I from rfl,
      J.residualPolynomial_eq I ha s hs, J.residual_eval I, I.z_mu]
    rfl
  have heps : (J.leading N).eval 1/J.den I N = I.epsilon N :=
    J.endpoint_ratio I (by positivity : (2/(2:ℝ)^N) ≠ 0) (family.terminal hN)
  have hPN : (J.leading N).eval 1 ≠ 0 :=
    ne_of_gt (family.leading_eval_one_pos hN (le_refl N))
  rw [cubicErrorPolynomial_coeff_two_forced,
    TwoTerm.perturbedError_eq_residual_add_forcing]
  change ((aeval H ((J.method I).realization.residualPolynomial N)).mulVec (0 : Fin 1 → ℝ) +
    ∑ s ∈ Finset.range N, (J.method I).forcingTail H N s
      ((0 : Fin 1 → ℝ)-((J.method I).gamma s • fun _ => -(rho/2)*
        ((J.method I).realization.residualPolynomial s).eval I.mu ^ 2))) 0 = _
  simp only [Matrix.mulVec_zero, zero_add, zero_sub, Finset.sum_apply]
  change (∑ s ∈ Finset.range N, (J.method I).forcingTail H N s
    (-((J.method I).gamma s • fun _ => -(rho/2)*
      ((J.method I).realization.residualPolynomial s).eval I.mu ^ 2)) 0) = _
  rw [show (rho/I.delta)*I.epsilon N*secondOrderCoefficient J I N =
    ∑ s ∈ Finset.range N, (rho/I.delta)*I.epsilon N*
      (J.endpointProfile N s*leadingRadius J I s) by
        dsimp [secondOrderCoefficient]
        rw [Finset.mul_sum]]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := Finset.mem_range.mp hs
  rw [TwoTerm.forcingTail_eq_memoryProduct, J.operator_tail I ha (s+1) (by omega) (by omega)]
  simp only [H, aeval_diagonal, Matrix.smul_mulVec,
    Matrix.mulVec_neg, Matrix.mulVec_smul, Matrix.mulVec_diagonal, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul]
  rw [J.spectralBlock_eval I, I.z_mu, hp s (by omega), ← heps]
  have hds : J.den I s ≠ 0 := ne_of_gt (ha s (by omega))
  have hdN : J.den I N ≠ 0 := ne_of_gt (ha N le_rfl)
  have hdsp : J.den I (s+1) ≠ 0 := ne_of_gt (ha (s+1) (by omega))
  dsimp [JacobiData.method, JacobiData.endpointProfile, leadingRadius]
  field_simp [hds, hdN, hdsp, hPN]

theorem cubicErrorPolynomial_coeff_one_terminal (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (rho : ℝ) :
    (cubicErrorPolynomial ((family.data N).method I) I.mu rho N).coeff 1 = I.epsilon N := by
  rw [cubicErrorPolynomial_coeff_one]
  change (((family.data N).realization I).residualPolynomial N).eval I.mu = _
  rw [(family.data N).residualPolynomial_eq I (family.admissible I hN) N le_rfl,
    (family.data N).terminal_residual I (by positivity : (2/(2:ℝ)^N) ≠ 0) (family.terminal hN),
    I.residual_eval, I.z_mu, T_eval_one]
  simp [SpectralInterval.epsilon]

theorem polynomial_second_order_factor (P : ℝ[X]) (hP : P.coeff 0 = 0) :
    P = C (P.coeff 1)*X + P.divX.divX*X^2 := by
  have h1 := divX_mul_X_add P
  have h2 := divX_mul_X_add P.divX
  rw [hP, C_0, add_zero] at h1
  rw [coeff_divX] at h2
  calc
    P = P.divX*X := h1.symm
    _ = (P.divX.divX*X+C (P.coeff 1))*X := by rw [h2]
    _ = _ := by ring

/-- A punctured second-order quotient of any polynomial has its expected limit. -/
theorem polynomial_second_order_limit (P : ℝ[X]) (hP : P.coeff 0 = 0) :
    Filter.Tendsto (fun r : ℝ => (P.eval r-P.coeff 1*r)/r^2)
      (nhdsWithin 0 {0}ᶜ) (nhds (P.coeff 2)) := by
  have hh : Filter.Tendsto (fun r : ℝ => P.divX.divX.eval r)
      (nhdsWithin 0 {0}ᶜ) (nhds (P.coeff 2)) := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_divX, zero_add, Nat.reduceAdd] using
      ((P.divX.divX.continuousAt (a := (0:ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ)))
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : r ≠ 0 := by simpa using hr
  have he := congrArg (fun Q : ℝ[X] => Q.eval r) (polynomial_second_order_factor P hP)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at he
  rw [he]
  field_simp
  ring

/-- The next remainder is cubic, which is stronger than a second-order little-o. -/
theorem polynomial_third_order_factor (P : ℝ[X]) (hP : P.coeff 0 = 0) :
    P = C (P.coeff 1)*X + C (P.coeff 2)*X^2 + P.divX.divX.divX*X^3 := by
  have hh := divX_mul_X_add P.divX.divX
  simp only [coeff_divX] at hh
  conv_lhs => rw [polynomial_second_order_factor P hP]
  conv_lhs => rhs; lhs; rw [← hh]
  ring

theorem polynomial_third_order_isBigO (P : ℝ[X]) (hP : P.coeff 0 = 0) :
    (fun r : ℝ => P.eval r-P.coeff 1*r-P.coeff 2*r^2)
      =O[nhds 0] (fun r : ℝ => r^3) := by
  have hb := (P.divX.divX.divX.continuousAt (a := (0 : ℝ))).tendsto.isBigO_one ℝ
  have hm := hb.mul (Asymptotics.isBigO_refl (fun r : ℝ => r^3) (nhds 0))
  simp only [one_mul] at hm
  convert hm using 1
  funext r
  have he := congrArg (fun Q : ℝ[X] => Q.eval r) (polynomial_third_order_factor P hP)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at he
  linarith

/-- The actual cubic run has an O(r³) remainder at its exact quadratic coefficient. -/
theorem cubic_weighted_remainder_isBigO (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (rho : ℝ) :
    (fun r : ℝ =>
      (((family.data N).method I).nonlinearError
        (fun v : Fin 1 → ℝ => fun i => I.mu*v i-rho/2*(v i)^2) (fun _ => r) N 0)-
      I.epsilon N*r-
      ((rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N)*r^2)
      =O[nhds 0] (fun r : ℝ => r^3) := by
  simpa only [cubicErrorPolynomial_eval, cubicErrorPolynomial_coeff_one_terminal family I hN rho,
    cubicErrorPolynomial_coeff_two family I hN rho] using
    polynomial_third_order_isBigO
      (cubicErrorPolynomial ((family.data N).method I) I.mu rho N)
      (cubicErrorPolynomial_coeff_zero _ _ _ _)

/-- The actual scalar nonlinear recurrence attains the weighted coefficient as
the initial error tends to zero. No unproved Taylor hypothesis is required. -/
theorem cubic_weighted_sharpness (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (rho : ℝ) :
    Filter.Tendsto (fun r : ℝ =>
      ((((family.data N).method I).nonlinearError
        (fun v : Fin 1 → ℝ => fun i => I.mu*v i-rho/2*(v i)^2) (fun _ => r) N 0)-
          I.epsilon N*r)/r^2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N)) := by
  have hh := polynomial_second_order_limit
    (cubicErrorPolynomial ((family.data N).method I) I.mu rho N)
    (cubicErrorPolynomial_coeff_zero _ _ _ _)
  simpa only [cubicErrorPolynomial_eval, cubicErrorPolynomial_coeff_one_terminal family I hN rho,
    cubicErrorPolynomial_coeff_two family I hN rho] using hh

/-- Sharpness also holds for the absolute terminal discrepancy. -/
theorem cubic_weighted_norm_sharpness (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (rho : ℝ) (hrho : 0 ≤ rho) :
    Filter.Tendsto (fun r : ℝ =>
      |(((family.data N).method I).nonlinearError
        (fun v : Fin 1 → ℝ => fun i => I.mu*v i-rho/2*(v i)^2) (fun _ => r) N 0)-
          I.epsilon N*r|/r^2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N)) := by
  have hc : 0 ≤ (rho/I.delta)*I.epsilon N*secondOrderCoefficient (family.data N) I N :=
    mul_nonneg (mul_nonneg (div_nonneg hrho I.delta_pos.le)
      (one_div_nonneg.mpr (I.den_pos N).le))
      (secondOrderCoefficient_nonneg _ I (family.admissible I hN) (family.endpointMax hN))
  simpa only [abs_div, abs_sq, abs_of_nonneg hc] using
    (cubic_weighted_sharpness family I hN rho).abs

end
end chebyshev1.Nonlinear
