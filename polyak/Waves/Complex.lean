import polyak.Interpolation.Data
import Mathlib.Analysis.Complex.Trigonometric

/-!
Article: (m), Lemma spectralinterp, and Appendix A's single-wave calculation.
Use: genuine planar data, their heavy-ball recurrence, and exact signed interpolation slacks.
Proof: complex powers, real coordinates, and the exponential/hyperbolic identities.
-/

noncomputable section

namespace polyak.Waves

open Interpolation

/-- Article: z=exp(t+iω). Use: nonzero geometric wave ratio. -/
def z (t ω : ℝ) : ℂ := Complex.exp ((t : ℂ) + (ω : ℂ) * Complex.I)

/-- Article: multiplier m. Use: the gradient forced by the normalized recurrence. -/
def multiplier (A B β : ℝ) (t ω : ℝ) : ℂ :=
  (z t ω + (β : ℂ) / z t ω - (A : ℂ)) / (B : ℂ)

/-- Article: wave with minimizer datum. Use: arbitrary infinite interpolation tables. -/
def position (t ω : ℝ) : Option ℕ → ℂ
  | none => 0
  | some k => z t ω ^ k

/-- Article: σₖ=mzᵏ. Use: prescribed wave gradients, including the minimizer. -/
def gradient (m : ℂ) (t ω : ℝ) (i : Option ℕ) : ℂ := m * position t ω i

/-- Article: prescribed ψₖ. Use: common scalar C in a wave or spectral mixture. -/
def value (m : ℂ) (C t ω : ℝ) : Option ℕ → ℝ
  | none => 0
  | some k => (C + 2 * m.re) / 4 * Complex.normSq (z t ω ^ k)

/-- Article: z is nonzero. Proof: exponentials never vanish. -/
theorem z_ne_zero (t ω : ℝ) : z t ω ≠ 0 := Complex.exp_ne_zero _

/-- Article: wave powers. Proof: the exponential addition law. -/
theorem z_pow (t ω : ℝ) (k : ℕ) :
    z t ω ^ k = Complex.exp ((k : ℂ) * ((t : ℂ) + (ω : ℂ) * Complex.I)) :=
  (Complex.exp_nat_mul _ _).symm

/-- Article: real coordinate of a wave. Proof: Euler's formula. -/
theorem z_pow_re (t ω : ℝ) (k : ℕ) :
    (z t ω ^ k).re = Real.exp (k * t) * Real.cos (k * ω) := by
  rw [z_pow, Complex.exp_re]
  simp

/-- Article: imaginary coordinate of a wave. Proof: Euler's formula. -/
theorem z_pow_im (t ω : ℝ) (k : ℕ) :
    (z t ω ^ k).im = Real.exp (k * t) * Real.sin (k * ω) := by
  rw [z_pow, Complex.exp_im]
  simp

/-- Article: exact wave growth. Proof: the norm of exp is exp of the real part. -/
theorem norm_z_pow (t ω : ℝ) (k : ℕ) : ‖z t ω ^ k‖ = Real.exp (k * t) := by
  rw [z_pow, Complex.norm_exp]
  simp

/-- Article: squared wave growth. Proof: square the norm identity. -/
theorem normSq_z_pow (t ω : ℝ) (k : ℕ) :
    Complex.normSq (z t ω ^ k) = Real.exp (2 * k * t) := by
  rw [Complex.normSq_eq_norm_sq, norm_z_pow, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Article: wave recurrence. Proof: multiply the defining equation for m by z^(k+1).
Use: no arbitrary recurrence hypothesis is added to a wave. -/
theorem recurrence (A B β t ω : ℝ) (hB : B ≠ 0) (k : ℕ) :
    z t ω ^ (k + 2) = (A : ℂ) * z t ω ^ (k + 1) +
      (B : ℂ) * (multiplier A B β t ω * z t ω ^ (k + 1)) -
      (β : ℂ) * z t ω ^ k := by
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB
  have hz := z_ne_zero t ω
  unfold multiplier
  rw [pow_add, pow_add]
  field_simp
  ring

/-- Article: R for one pair, in complex coordinates. Use: explicit factorization of the radius. -/
theorem pair_radius (scale w m : ℂ) :
    (1 / 4 : ℝ) * (‖scale * w - scale‖ ^ 2 - ‖m * (scale * w) - m * scale‖ ^ 2) =
      Complex.normSq scale * ((1 - Complex.normSq m) / 4 * Complex.normSq (w - 1)) := by
  have h₁ : scale * w - scale = scale * (w - 1) := by ring
  have h₂ : m * (scale * w) - m * scale = m * (scale * (w - 1)) := by ring
  rw [h₁, h₂]
  simp only [Complex.sq_norm, Complex.normSq_mul]
  ring

/-- Article: T for one pair. Proof: expand real and imaginary coordinates; no analytic assumption. -/
theorem pair_discrepancy (scale w m : ℂ) (C : ℝ) :
    (C + 2 * m.re) / 4 * Complex.normSq (scale * w) -
      (C + 2 * m.re) / 4 * Complex.normSq scale -
      (1 / 2 : ℝ) * inner ℝ (m * scale + m * (scale * w)) (scale * w - scale) =
      Complex.normSq scale * (C / 4 * (Complex.normSq w - 1) - m.im * w.im) := by
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- Article: Rⱼ,ⱼ₊ₙ. Proof: the pair factorization and z^(j+n)=z^j z^n. -/
theorem datumR_wave (m : ℂ) (t ω : ℝ) (j n : ℕ) :
    datumR (position t ω) (gradient m t ω) (some j) (some (j + n)) =
      Complex.normSq (z t ω ^ j) *
        ((1 - Complex.normSq m) / 4 * Complex.normSq (z t ω ^ n - 1)) := by
  simp only [datumR, position, gradient, pow_add]
  exact pair_radius _ _ _

/-- Article: Tⱼ,ⱼ₊ₙ. Proof: the coordinate calculation of the pair discrepancy. -/
theorem datumT_wave (m : ℂ) (C t ω : ℝ) (j n : ℕ) :
    datumT (position t ω) (gradient m t ω) (value m C t ω) (some j) (some (j + n)) =
      Complex.normSq (z t ω ^ j) *
        (C / 4 * (Complex.normSq (z t ω ^ n) - 1) - m.im * (z t ω ^ n).im) := by
  simp only [datumT, position, gradient, value, pow_add]
  exact pair_discrepancy _ _ _ _

/-- Article: minimizer pair radius. Proof: the datum at the origin vanishes. -/
theorem datumR_star (m : ℂ) (t ω : ℝ) (j : ℕ) :
    datumR (position t ω) (gradient m t ω) none (some j) =
      Complex.normSq (z t ω ^ j) * ((1 - Complex.normSq m) / 4) := by
  simp only [datumR, position, gradient, mul_zero, sub_zero, Complex.sq_norm,
    Complex.normSq_mul]
  ring

/-- Article: minimizer pair discrepancy. Proof: the prescribed value cancels Re(m)/2. -/
theorem datumT_star (m : ℂ) (C t ω : ℝ) (j : ℕ) :
    datumT (position t ω) (gradient m t ω) (value m C t ω) none (some j) =
      Complex.normSq (z t ω ^ j) * (C / 4) := by
  simp only [datumT, position, gradient, value, mul_zero, zero_add, sub_zero]
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring



/-- Article: hyperbolic conversion of the radial difference. Proof: exponential definitions. -/
theorem exp_two_sub_one (x : ℝ) :
    Real.exp (2 * x) - 1 = 2 * Real.exp x * Real.sinh x := by
  rw [Real.sinh_eq]
  have hp : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hsq : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [hsq]
  nlinarith

/-- Article: hyperbolic conversion of the radial sum. Proof: exponential definitions. -/
theorem exp_two_add_one (x : ℝ) :
    Real.exp (2 * x) + 1 = 2 * Real.exp x * Real.cosh x := by
  rw [Real.cosh_eq]
  have hp : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hsq : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [hsq]
  nlinarith

/-- Article: squared chord length. Proof: expand the norm in real coordinates. -/
theorem normSq_sub_one (w : ℂ) :
    Complex.normSq (w - 1) = Complex.normSq w + 1 - 2 * w.re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

/-- Article: squared wave chord length. Proof: the radial sum identity and Euler's formula. -/
theorem normSq_z_pow_sub_one (t ω : ℝ) (n : ℕ) :
    Complex.normSq (z t ω ^ n - 1) =
      2 * Real.exp (n * t) * (Real.cosh (n * t) - Real.cos (n * ω)) := by
  rw [normSq_sub_one, normSq_z_pow, z_pow_re,
    show (2 : ℝ) * n * t = 2 * (n * t) by ring, exp_two_add_one]
  ring

/-- Article: all signed wave slacks in (waveslacks). Use: δ=1 and δ=-1 give both signs.
Proof: the exact pair formulas and hyperbolic exponential identities. -/
theorem datum_slack (m : ℂ) (C t ω δ : ℝ) (j n : ℕ) :
    datumR (position t ω) (gradient m t ω) (some j) (some (j + n)) +
      δ * datumT (position t ω) (gradient m t ω) (value m C t ω)
        (some j) (some (j + n)) =
    (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
      ((1 - Complex.normSq m) * (Real.cosh (n * t) - Real.cos (n * ω)) -
        δ * (2 * m.im * Real.sin (n * ω)) + δ * C * Real.sinh (n * t)) := by
  rw [datumR_wave, datumT_wave, normSq_z_pow, normSq_z_pow,
    normSq_z_pow_sub_one, z_pow_im,
    show (2 : ℝ) * n * t = 2 * (n * t) by ring, exp_two_sub_one,
    show ((2 : ℝ) * j + n) * t = 2 * j * t + n * t by ring, Real.exp_add]
  ring

/-- Article: signed slacks against the minimizer. Proof: the exact origin pair formulas. -/
theorem datum_star_slack (m : ℂ) (C t ω δ : ℝ) (j : ℕ) :
    datumR (position t ω) (gradient m t ω) none (some j) +
      δ * datumT (position t ω) (gradient m t ω) (value m C t ω) none (some j) =
      (1 / 4 : ℝ) * Real.exp (2 * j * t) * ((1 - Complex.normSq m) + δ * C) := by
  rw [datumR_star, datumT_star, normSq_z_pow]
  ring

end polyak.Waves
