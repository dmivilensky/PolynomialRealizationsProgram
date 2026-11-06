import nesterov.Phase.Geometry

/-!
Article: Lemma `angle`, Equations (defect) and their stationary lag-one symbol.
Use: literal complex real-part identities with any given polar representative.
-/

namespace nesterov.Phase
noncomputable section
open Spectral Set

theorem complex_defect_coordinates (g s ω : ℝ) :
    ((1 - Complex.exp ((ω : ℂ) * Complex.I)) * ((g : ℂ) - 2 * Complex.I * s)).re =
      g * (1 - Real.cos ω) - 2 * s * Real.sin ω ∧
    ((1 - Complex.exp (-(ω : ℂ) * Complex.I)) * ((g : ℂ) - 2 * Complex.I * s)).re =
      g * (1 - Real.cos ω) + 2 * s * Real.sin ω := by
  simp only [Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.mul_re, Complex.mul_im]
  constructor <;> ring

/-- Both literal complex expressions in Equation (defect), for an arbitrary
polar representative supplied in the hypothesis. -/
theorem complex_defect_polar {g s R Θ : ℝ}
    (hpolar : (g : ℂ) - 2 * Complex.I * s =
      (R : ℂ) * Complex.exp (-(Θ : ℂ) * Complex.I)) (ω : ℝ) :
    ((1 - Complex.exp ((ω : ℂ) * Complex.I)) * ((g : ℂ) - 2 * Complex.I * s)).re =
      2 * R * Real.sin (ω / 2) * Real.sin ((ω - 2 * Θ) / 2) ∧
    ((1 - Complex.exp (-(ω : ℂ) * Complex.I)) * ((g : ℂ) - 2 * Complex.I * s)).re =
      2 * R * Real.sin (ω / 2) * Real.sin ((ω + 2 * Θ) / 2) := by
  have hr : g = R * Real.cos Θ := by
    have hh := congrArg Complex.re hpolar
    simp only [Complex.exp_mul_I] at hh
    simpa [← Complex.ofReal_cos, ← Complex.ofReal_sin] using hh
  have hi : 2 * s = R * Real.sin Θ := by
    have hh := congrArg Complex.im hpolar
    simp only [Complex.exp_mul_I] at hh
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hh
    linarith only [hh]
  have hcoord := complex_defect_coordinates g s ω
  have hh := lag_one_polar_identity R Θ ω
  constructor
  · rw [hcoord.1, hr, hi]
    exact hh.1
  · rw [hcoord.2, hr, hi]
    exact hh.2

theorem complex_defect_phase (g s ω : ℝ) :
    ((1 - Complex.exp ((ω : ℂ) * Complex.I)) * ((g : ℂ) - 2 * Complex.I * s)).re =
      2 * magnitude g s * Real.sin (ω / 2) * Real.sin ((ω - 2 * angle g s) / 2) ∧
    ((1 - Complex.exp (-(ω : ℂ) * Complex.I)) * ((g : ℂ) - 2 * Complex.I * s)).re =
      2 * magnitude g s * Real.sin (ω / 2) * Real.sin ((ω + 2 * angle g s) / 2) :=
  complex_defect_polar (polar_representation g s) ω

/-- The generic stationary lag-one symbol is exactly the source coefficient
times sin(Θ-ω/2).  Characteristic factors have the same product for the
repository convention v-λu and the article convention λu-v. -/
theorem stationary_lag_one_phase_identity (M : StationaryMethod) {μ L ω : ℝ}
    (hμL : μ < L) (hω : ω ∈ Icc (0 : ℝ) Real.pi) :
    let ζ := Complex.exp ((ω : ℂ) * Complex.I)
    let a := M.symbolPair μ L 0
    ((1 - ζ) * M.characteristic μ ζ * star (M.characteristic L ζ)).re =
      (L - μ) ^ 2 / 2 * magnitude (g a (frequency ω)) (skew a (frequency ω)) *
        Real.sin (ω / 2) *
        Real.sin (angle (g a (frequency ω)) (skew a (frequency ω)) - ω / 2) := by
  dsimp only
  let ζ := Complex.exp ((ω : ℂ) * Complex.I)
  let a := M.symbolPair μ L 0
  have hz : polyak.Waves.z 0 (Real.arccos (frequency ω)) = ζ := by
    rw [arccos_frequency hω]
    simp [polyak.Waves.z, ζ]
  have hf := stationary_factor M hμL 0 (frequency ω)
  rw [hz] at hf
  have hrel : ((1 - ζ) * ((g a (frequency ω) : ℂ) -
      2 * Complex.I * skew a (frequency ω))).re =
      -(4 / (L - μ) ^ 2) *
        ((1 - ζ) * M.characteristic μ ζ * star (M.characteristic L ζ)).re := by
    rw [hf]
    have he : (1 - ζ) * (-((4 / (L - μ) ^ 2 : ℝ) : ℂ) * M.characteristic μ ζ *
        star (M.characteristic L ζ)) =
        -((4 / (L - μ) ^ 2 : ℝ) : ℂ) *
          ((1 - ζ) * M.characteristic μ ζ * star (M.characteristic L ζ)) := by ring
    rw [he]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  have hd := (complex_defect_phase (g a (frequency ω)) (skew a (frequency ω)) ω).1
  change ((1 - ζ) * _).re = _ at hd
  rw [hrel] at hd
  rw [show (ω - 2 * angle (g a (frequency ω)) (skew a (frequency ω))) / 2 =
    -(angle (g a (frequency ω)) (skew a (frequency ω)) - ω / 2) by ring,
    Real.sin_neg] at hd
  have hwidth : L - μ ≠ 0 := sub_ne_zero.mpr hμL.ne'
  field_simp [hwidth] at hd ⊢
  linear_combination -hd / 2

theorem stationary_lag_one_positive_factor (M : StationaryMethod) {μ L ω : ℝ}
    (hμL : μ < L) (hω : ω ∈ Ioc (0 : ℝ) Real.pi)
    (hne : g (M.symbolPair μ L 0) (frequency ω) ≠ 0 ∨
      skew (M.symbolPair μ L 0) (frequency ω) ≠ 0) :
    let ζ := Complex.exp ((ω : ℂ) * Complex.I)
    let a := M.symbolPair μ L 0
    ∃ C : ℝ, 0 < C ∧
      ((1 - ζ) * M.characteristic μ ζ * star (M.characteristic L ζ)).re =
        C * Real.sin (angle (g a (frequency ω)) (skew a (frequency ω)) - ω / 2) := by
  dsimp only
  refine ⟨(L - μ) ^ 2 / 2 *
    magnitude (g (M.symbolPair μ L 0) (frequency ω)) (skew (M.symbolPair μ L 0) (frequency ω)) *
      Real.sin (ω / 2), ?_, stationary_lag_one_phase_identity M hμL ⟨hω.1.le, hω.2⟩⟩
  exact mul_pos (mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr hμL)) (by norm_num))
    (magnitude_pos hne)) (Real.sin_pos_of_pos_of_lt_pi (by linarith [hω.1])
      (by linarith [hω.2, Real.pi_pos]))

end
end nesterov.Phase
