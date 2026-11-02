import jacobi.Reference.WaveDerivatives

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
For every complex frequency the actual hypergeometric reference solution
solves the precise printed Poeschl--Teller Schrodinger equation on the
whole physical interior. Its derivatives are genuine spatial derivatives;
the source frequency and potential are the literal original formulas.
Use: transforms the genuine hypergeometric equation into the original reference differential equation.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual coordinate Jacobian squared is exactly the Gauss-to-Schrodinger leading coefficient.
Use: transforms the genuine hypergeometric equation into the original reference differential equation.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: substitute the literal coordinate and use the community sine-square identity. -/
theorem coordinate_leading (t : ℝ) : coordinateSlope t^2=Real.pi^2*coordinate t*(1-coordinate t) := by
  dsimp [coordinateSlope,coordinate]
  nlinarith [congrArg (fun x : ℝ => Real.pi^2*x) (Real.sin_sq_add_cos_sq (Real.pi*t))]

/-- The actual reference logarithmic slope and coordinate acceleration give exactly the Gauss first-derivative coefficient.
Use: identifies the first-order term in the true hypergeometric-to-reference substitution.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: cancel the true nonzero physical sine in the actual coefficients and collect the cosine terms. -/
theorem coordinate_first (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) :
    2*weightLogSlope a t*coordinateSlope t+coordinateAcceleration t=
      Real.pi^2*(gamma a+1/2-(2*gamma a+1)*coordinate t) := by
  dsimp [weightLogSlope,coordinateSlope,coordinateAcceleration,coordinate]
  field_simp [(sine_pos ht).ne']
  ring

/-- The true reference prefactor gives exactly the original zeroth potential term, independent of the frequency.
Use: supplies the precise Poeschl--Teller potential in the complex reference Schrodinger equation.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: specialize the already proved exact sine-power coefficient identity to original polynomial degree zero. -/
theorem weight_potential (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) :
    weightLogAcceleration a t+weightLogSlope a t^2-potential a t=
      -(Real.pi^2*gamma a^2+ jacobi.Jacobi.endpointCorrection a) := by
  have h := zeroth_coefficient a 0 ht
  dsimp [eigenvalue] at h
  norm_num only [Nat.cast_zero,zero_add,mul_zero,zero_mul] at h
  linarith

/-- The actual complex source reference solution satisfies its exact original Schrodinger equation for every complex frequency.
Use: supplies the reference equation at arbitrary complex energy to the actual GL kernel and transformed equation of Proposition C.2.
Article: jacobi, Lemma C.1.
Proof: apply the proved genuine Gauss equation at the actual physical
coordinate. The three exact coefficient identities transform its leading,
first and zeroth terms into the true spatial acceleration and the literal
source potential. Every convergence and order premise is discharged. -/
theorem wave_equation {a : ℝ} (ha : -1<a) (omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    -waveAcceleration a omega t+(potential a t:ℂ)*wave a omega t=
      ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)*wave a omega t := by
  -- This is an unconditional equation for the actual community special function and its genuine original spatial derivatives.
  let A : ℂ := (gamma a:ℂ)-omega/(Real.pi:ℂ)
  let B : ℂ := (gamma a:ℂ)+omega/(Real.pi:ℂ)
  let C : ℂ := (gamma a:ℂ)+1/2
  let x : ℂ := coordinate t
  have hC : 0<C.re := by dsimp [C]; norm_num; linarith [(parameters ha).1]
  have h := Hypergeometric.equation (a := A) (b := B) hC (coordinate_norm_lt_one ht)
  change x*(1-x)*deriv (deriv (waveCore a omega)) x+
    (C-(A+B+1)*x)*deriv (waveCore a omega) x-A*B*waveCore a omega x=0 at h
  have h2 : (coordinateSlope t:ℂ)^2=(Real.pi:ℂ)^2*x*(1-x) := by
    dsimp [x]
    exact_mod_cast coordinate_leading t
  have h1 : 2*(weightLogSlope a t:ℂ)*(coordinateSlope t:ℂ)+(coordinateAcceleration t:ℂ)=
      (Real.pi:ℂ)^2*(C-(A+B+1)*x) := by
    have hr := congrArg Complex.ofReal (coordinate_first a ht)
    dsimp [A,B,C,x]
    push_cast at hr
    linear_combination hr
  have h0 : (weightLogAcceleration a t:ℂ)+(weightLogSlope a t:ℂ)^2+
      (jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2-(potential a t:ℂ)= -(Real.pi:ℂ)^2*A*B := by
    have hr := congrArg Complex.ofReal (weight_potential a ht)
    push_cast at hr
    dsimp [A,B]
    have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
    linear_combination hr
  unfold waveAcceleration wave
  change -((weight a t:ℂ)*(((weightLogAcceleration a t:ℂ)+(weightLogSlope a t:ℂ)^2)*waveCore a omega x+
    (2*(weightLogSlope a t:ℂ)*(coordinateSlope t:ℂ)+(coordinateAcceleration t:ℂ))*deriv (waveCore a omega) x+
    (coordinateSlope t:ℂ)^2*deriv (deriv (waveCore a omega)) x))+
    (potential a t:ℂ)*((weight a t:ℂ)*waveCore a omega x)=
      ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)*((weight a t:ℂ)*waveCore a omega x)
  linear_combination -(weight a t:ℂ)*(Real.pi:ℂ)^2*h-
    (weight a t:ℂ)*deriv (deriv (waveCore a omega)) x*h2-
    (weight a t:ℂ)*deriv (waveCore a omega) x*h1-
    (weight a t:ℂ)*waveCore a omega x*h0

end
end jacobi.Reference
