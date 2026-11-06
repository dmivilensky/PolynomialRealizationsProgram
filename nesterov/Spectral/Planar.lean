import polyak.Waves.Complex

/-! Exact planar calculations for two independent amplitudes. No quotient is used. -/
noncomputable section
namespace nesterov.Spectral.Planar
open polyak.Interpolation polyak.Waves

def position (u : ℂ) (t ω : ℝ) (i : Option ℕ) : ℂ := u * polyak.Waves.position t ω i

def gradient (p : ℂ) (t ω : ℝ) (i : Option ℕ) : ℂ := p * polyak.Waves.position t ω i

def value (u p : ℂ) (C t ω : ℝ) : Option ℕ → ℝ
  | none => 0
  | some k => (C + 2 * (p * star u).re) / 4 * Complex.normSq (z t ω ^ k)

theorem pair_radius (scale w u p : ℂ) :
    (1 / 4 : ℝ) * (‖u * (scale * w) - u * scale‖ ^ 2 -
      ‖p * (scale * w) - p * scale‖ ^ 2) =
      Complex.normSq scale * ((Complex.normSq u - Complex.normSq p) / 4 *
        Complex.normSq (w - 1)) := by
  have hu : u * (scale * w) - u * scale = u * (scale * (w - 1)) := by ring
  have hp : p * (scale * w) - p * scale = p * (scale * (w - 1)) := by ring
  rw [hu, hp]
  simp only [Complex.sq_norm, Complex.normSq_mul]
  ring

theorem pair_discrepancy (scale w u p : ℂ) (C : ℝ) :
    (C + 2 * (p * star u).re) / 4 * Complex.normSq (scale * w) -
      (C + 2 * (p * star u).re) / 4 * Complex.normSq scale -
      (1 / 2 : ℝ) * inner ℝ (p * scale + p * (scale * w))
        (u * (scale * w) - u * scale) =
      Complex.normSq scale * (C / 4 * (Complex.normSq w - 1) -
        (p * star u).im * w.im) := by
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.star_def]
  ring

/-- Article: Rⱼ,ⱼ₊ₙ. Proof: the pair factorization and z^(j+n)=z^j z^n. -/
theorem datumR_wave (u p : ℂ) (t ω : ℝ) (j n : ℕ) :
    datumR (position u t ω) (gradient p t ω) (some j) (some (j + n)) =
      Complex.normSq (z t ω ^ j) *
        ((Complex.normSq u - Complex.normSq p) / 4 * Complex.normSq (z t ω ^ n - 1)) := by
  simp only [datumR, position, gradient, polyak.Waves.position, pow_add]
  exact pair_radius _ _ _ _

/-- Article: Tⱼ,ⱼ₊ₙ. Proof: the coordinate calculation of the pair discrepancy. -/
theorem datumT_wave (u p : ℂ) (C t ω : ℝ) (j n : ℕ) :
    datumT (position u t ω) (gradient p t ω) (value u p C t ω) (some j) (some (j + n)) =
      Complex.normSq (z t ω ^ j) *
        (C / 4 * (Complex.normSq (z t ω ^ n) - 1) - (p * star u).im * (z t ω ^ n).im) := by
  simp only [datumT, position, gradient, polyak.Waves.position, value, pow_add]
  exact pair_discrepancy _ _ _ _ _

/-- Article: minimizer pair radius. Proof: the datum at the origin vanishes. -/
theorem datumR_star (u p : ℂ) (t ω : ℝ) (j : ℕ) :
    datumR (position u t ω) (gradient p t ω) none (some j) =
      Complex.normSq (z t ω ^ j) * ((Complex.normSq u - Complex.normSq p) / 4) := by
  simp only [datumR, position, gradient, polyak.Waves.position, mul_zero, sub_zero, Complex.sq_norm,
    Complex.normSq_mul]
  ring

/-- Article: minimizer pair discrepancy. Proof: the prescribed value cancels Re(m)/2. -/
theorem datumT_star (u p : ℂ) (C t ω : ℝ) (j : ℕ) :
    datumT (position u t ω) (gradient p t ω) (value u p C t ω) none (some j) =
      Complex.normSq (z t ω ^ j) * (C / 4) := by
  simp only [datumT, position, gradient, polyak.Waves.position, value, mul_zero, zero_add, sub_zero]
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply, Complex.star_def]
  ring



/-- Article: all signed wave slacks in (waveslacks). Use: δ=1 and δ=-1 give both signs.
Proof: the exact pair formulas and hyperbolic exponential identities. -/
theorem datum_slack (u p : ℂ) (C t ω δ : ℝ) (j n : ℕ) :
    datumR (position u t ω) (gradient p t ω) (some j) (some (j + n)) +
      δ * datumT (position u t ω) (gradient p t ω) (value u p C t ω)
        (some j) (some (j + n)) =
    (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
      ((Complex.normSq u - Complex.normSq p) * (Real.cosh (n * t) - Real.cos (n * ω)) -
        δ * (2 * (p * star u).im * Real.sin (n * ω)) + δ * C * Real.sinh (n * t)) := by
  rw [datumR_wave, datumT_wave, normSq_z_pow, normSq_z_pow,
    normSq_z_pow_sub_one, z_pow_im,
    show (2 : ℝ) * n * t = 2 * (n * t) by ring, exp_two_sub_one,
    show ((2 : ℝ) * j + n) * t = 2 * j * t + n * t by ring, Real.exp_add]
  ring

/-- Article: signed slacks against the minimizer. Proof: the exact origin pair formulas. -/
theorem datum_star_slack (u p : ℂ) (C t ω δ : ℝ) (j : ℕ) :
    datumR (position u t ω) (gradient p t ω) none (some j) +
      δ * datumT (position u t ω) (gradient p t ω) (value u p C t ω) none (some j) =
      (1 / 4 : ℝ) * Real.exp (2 * j * t) * ((Complex.normSq u - Complex.normSq p) + δ * C) := by
  rw [datumR_star, datumT_star, normSq_z_pow]
  ring

end nesterov.Spectral.Planar
