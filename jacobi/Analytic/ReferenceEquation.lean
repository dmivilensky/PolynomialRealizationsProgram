import jacobi.Analytic.ReferenceDifferential
import jacobi.Reference.PotentialBounds

/-!
Article: jacobi, Lemma C.1.
The actual complex-order reference solution obeys its original
singular equation. The singular potential and logarithmic slope
have common bounds on every bounded complex-order set.
Use: turns the Gauss equation into the actual reference Schrodinger equation.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set jacobi.Reference
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true logarithmic reference coefficients retain the exact singular-potential identity at complex order.
Use: turns the Gauss equation into the actual reference Schrodinger equation.
Article: jacobi, Lemma C.1.
Proof: clear the nonzero physical sine denominator. The remaining
identity is gamma squared times the genuine sine-square circle identity. -/
theorem weight_potential (a : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    weightLogAcceleration a t+weightLogSlope a t^2-singularPotential a t=
      -(Real.pi:ℂ)^2*gamma a^2 := by
  have hs : (Real.sin (Real.pi*t):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sine_pos ht).ne'
  have hcircle : (Real.sin (Real.pi*t):ℂ)^2+(Real.cos (Real.pi*t):ℂ)^2=1 :=
    by exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi*t)
  unfold weightLogAcceleration weightLogSlope singularPotential
  field_simp [hs]
  linear_combination (gamma a)^2*hcircle

/-- The genuine reference acceleration satisfies the original frequency equation for every complex order with positive endpoint real part.
Use: proves the actual differential energy inequality used in complex-order high-frequency bounds.
Article: jacobi, Lemma C.1.
Proof: apply the proved Gauss equation at the original physical
coordinate. Its second- and first-derivative coefficients are exactly
the coordinate Jacobian square and transformed logarithmic slope.
The preceding exact complex potential identity fixes the zeroth term. -/
theorem waveAcceleration_frequency {a : ℂ} (ha : 0<(gamma a).re) (omega : ℂ)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    waveAcceleration a omega t=(singularPotential a t-omega^2)*wave a omega t := by
  -- All three transformed coefficients are identities of the actual spatial derivatives.
  let A := gamma a-omega/(Real.pi:ℂ)
  let B := gamma a+omega/(Real.pi:ℂ)
  let C := gamma a+1/2
  let x : ℂ := coordinate t
  have hC : 0<C.re := by dsimp [C]; norm_num; linarith
  have h := jacobi.Reference.Hypergeometric.equation (a := A) (b := B) hC (coordinate_norm_lt_one ht)
  change x*(1-x)*deriv (deriv (waveCore a omega)) x+
    (C-(A+B+1)*x)*deriv (waveCore a omega) x-A*B*waveCore a omega x=0 at h
  have h2 : (coordinateSlope t:ℂ)^2=(Real.pi:ℂ)^2*x*(1-x) := by
    dsimp [x]
    exact_mod_cast coordinate_leading t
  have hs : (Real.sin (Real.pi*t):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sine_pos ht).ne'
  have hsin : Complex.sin ((Real.pi:ℂ)*(t:ℂ))≠0 := by
    simpa only [Complex.ofReal_sin,Complex.ofReal_mul] using hs
  have h1 : 2*weightLogSlope a t*(coordinateSlope t:ℂ)+(coordinateAcceleration t:ℂ)=
      (Real.pi:ℂ)^2*(C-(A+B+1)*x) := by
    dsimp [weightLogSlope,coordinateSlope,coordinateAcceleration,coordinate,A,B,C,x]
    push_cast
    field_simp [hsin]
    ring
  have h0 : weightLogAcceleration a t+weightLogSlope a t^2+omega^2-singularPotential a t=
      -(Real.pi:ℂ)^2*A*B := by
    have hp := weight_potential a ht
    have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    dsimp [A,B]
    field_simp [hpi]
    linear_combination hp
  unfold waveAcceleration wave
  change weight a t*((weightLogAcceleration a t+weightLogSlope a t^2)*waveCore a omega x+
    (2*weightLogSlope a t*(coordinateSlope t:ℂ)+(coordinateAcceleration t:ℂ))*deriv (waveCore a omega) x+
    (coordinateSlope t:ℂ)^2*deriv (deriv (waveCore a omega)) x)=
      (singularPotential a t-omega^2)*(weight a t*waveCore a omega x)
  linear_combination weight a t*(Real.pi:ℂ)^2*h+
    weight a t*deriv (deriv (waveCore a omega)) x*h2+
    weight a t*deriv (waveCore a omega) x*h1+weight a t*waveCore a omega x*h0

/-- The complex reference singular potential has a common inverse-square bound on every bounded set of endpoint exponents.
Use: the same integrating factor propagates every order in the GL disk.
Article: jacobi, Lemma C.1.
Proof: the actual sine is at least twice the physical half-interval
coordinate. Bound the complex numerator by G*(G+1)*pi squared and divide
by this strictly positive squared sine lower bound. -/
theorem singularPotential_uniform_bound {G : ℝ} (hG : 0<G) {a : ℂ}
    (ha : ‖gamma a‖≤G) {t : ℝ} (ht : t∈Ioc 0 (1/2)) :
    ‖singularPotential a t‖≤(G*(G+1)*Real.pi^2/4)/t^2 := by
  -- The constant is independent of the complex order throughout its genuine bounded set.
  have htp : 0<t := ht.1
  have hs := half_sine_lower ht
  have hsp : 0<Real.sin (Real.pi*t) := (by linarith [ht.1] : (0:ℝ)<2*t).trans_le hs
  have hsq : 4*t^2≤Real.sin (Real.pi*t)^2 := by nlinarith [sq_nonneg (Real.sin (Real.pi*t)-2*t)]
  have hgm : ‖gamma a-1‖≤G+1 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hn : ‖gamma a*(gamma a-1)‖≤G*(G+1) := by
    rw [norm_mul]
    exact mul_le_mul ha hgm (norm_nonneg _) hG.le
  rw [singularPotential,norm_div,norm_mul,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos hsp]
  have hh := div_le_div₀ (by positivity : 0≤G*(G+1)*Real.pi^2)
    (mul_le_mul_of_nonneg_right hn (sq_nonneg Real.pi)) (by positivity : (0:ℝ)<4*t^2) hsq
  exact hh.trans_eq (by ring)

/-- The actual complex logarithmic slope has a common inverse-distance bound on a bounded order set.
Use: converts the initial core derivative bound into the true initial wave slope bound.
Article: jacobi, Lemma C.1.
Proof: cosine has absolute value at most one, the exponent norm is at
most G, and the physical sine is at least twice its positive coordinate. -/
theorem weightLogSlope_uniform_bound {G : ℝ} (hG : 0<G) {a : ℂ}
    (ha : ‖gamma a‖≤G) {t : ℝ} (ht : t∈Ioc 0 (1/2)) :
    ‖weightLogSlope a t‖≤(G*Real.pi/2)/t := by
  -- The real sine denominator is positive and at least 2*t on the entire physical half interval.
  have hs := half_sine_lower ht
  have hsp : 0<Real.sin (Real.pi*t) := (by linarith [ht.1] : (0:ℝ)<2*t).trans_le hs
  rw [weightLogSlope,norm_div,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,abs_of_pos hsp]
  have hn : ‖gamma a‖*Real.pi*|Real.cos (Real.pi*t)|≤G*Real.pi :=
    (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans
      (mul_le_mul_of_nonneg_right ha Real.pi_pos.le)
  exact (div_le_div₀ (by positivity : 0≤G*Real.pi) hn
    (by linarith [ht.1] : (0:ℝ)<2*t) hs).trans_eq (by ring)

end
end jacobi.ComplexReference
