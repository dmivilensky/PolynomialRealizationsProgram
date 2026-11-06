import nesterov.Phase.Geometry

/-!
Article: §4, the stable phase on the closed endpoint ω=π.
Use: complete the source statement Θ(ω)∈(0,π] for every 0<ω≤π,
including the negative real endpoint of the principal argument.
-/

namespace nesterov.Phase
noncomputable section
open Spectral Set

theorem angle_negative_real {g : ℝ} (hg : g < 0) : angle g 0 = Real.pi := by
  simpa only [angle, mode, Complex.ofReal_zero, mul_zero, add_zero] using
    Complex.arg_ofReal_of_neg hg

theorem endpoint_wave : polyak.Waves.z 0 (Real.arccos (frequency Real.pi)) = -1 := by
  rw [arccos_frequency ⟨Real.pi_pos.le, le_rfl⟩]
  apply Complex.ext
  · have hh := polyak.Waves.z_pow_re 0 Real.pi 1
    simpa using hh
  · have hh := polyak.Waves.z_pow_im 0 Real.pi 1
    simpa using hh

theorem stable_characteristic_neg_one_pos (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (hstable : q.Stable μ L) {lam : ℝ}
    (hlam : lam ∈ Icc μ L) :
    0 < 2 * (1 + q.beta) - q.stepSize * lam * (1 + 2 * q.tau) := by
  have hh := (q.stable_iff hμ hμL).mp hstable
  have hmul : q.stepSize * lam * (1 + 2 * q.tau) ≤
      q.stepSize * L * (1 + 2 * q.tau) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam.2 q.step_pos.le)
      (by linarith [q.tau_nonneg])
  linarith

/-- The endpoint amplitudes have strictly negative g and zero skew.  This
retains the strict stability hypothesis at the real point -1. -/
theorem momentum_endpoint_pair (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (hstable : q.Stable μ L) :
    g ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0)
        (frequency Real.pi) < 0 ∧
      skew ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0)
        (frequency Real.pi) = 0 := by
  let a := (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0
  let A := 2 * (1 + q.beta) - q.stepSize * μ * (1 + 2 * q.tau)
  let B := 2 * (1 + q.beta) - q.stepSize * L * (1 + 2 * q.tau)
  let k := 4 / (q.stepSize ^ 2 * (L - μ) ^ 2)
  have hA : 0 < A := stable_characteristic_neg_one_pos q hμ hμL hstable ⟨le_rfl, hμL.le⟩
  have hB : 0 < B := stable_characteristic_neg_one_pos q hμ hμL hstable ⟨hμL.le, le_rfl⟩
  have hk : 0 < k := div_pos (by norm_num)
    (mul_pos (sq_pos_of_pos q.step_pos) (sq_pos_of_pos (sub_pos.mpr hμL)))
  have hf : (g a (frequency Real.pi) : ℂ) -
      2 * Complex.I * skew a (frequency Real.pi) = -(k : ℂ) * (A : ℂ) * (B : ℂ) := by
    have hh := momentum_factor (β := q.beta) (τ := q.tau) hμL q.step_pos.ne' 0
      (frequency Real.pi)
    rw [endpoint_wave, Quadratic.characteristic_neg_one, Quadratic.characteristic_neg_one] at hh
    simpa only [Complex.star_def, Complex.conj_ofReal] using hh
  have hr : g a (frequency Real.pi) = -k * A * B := by
    simpa using congrArg Complex.re hf
  have hi : -2 * skew a (frequency Real.pi) = 0 := by
    simpa using congrArg Complex.im hf
  change g a (frequency Real.pi) < 0 ∧ skew a (frequency Real.pi) = 0
  constructor
  · rw [hr]
    nlinarith only [mul_pos (mul_pos hk hA) hB]
  · linarith only [hi]

theorem momentumAngle_pi (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (hstable : q.Stable μ L) :
    momentumAngle q μ L Real.pi = Real.pi := by
  have hh := momentum_endpoint_pair q hμ hμL hstable
  unfold momentumAngle
  rw [hh.2]
  exact angle_negative_real hh.1

/-- The source's full phase range includes its negative real endpoint. -/
theorem momentumAngle_mem_Ioc (q : Momentum.Tuning) {μ L ω : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (hstable : q.Stable μ L)
    (hω : ω ∈ Ioc (0 : ℝ) Real.pi) : momentumAngle q μ L ω ∈ Ioc (0 : ℝ) Real.pi := by
  rcases hω.2.lt_or_eq with hlt | rfl
  · have hh := momentumAngle_pos_lt_pi q hμL ⟨hω.1, hlt⟩
    exact ⟨hh.1, hh.2.le⟩
  · rw [momentumAngle_pi q hμ hμL hstable]
    exact ⟨Real.pi_pos, le_rfl⟩

end
end nesterov.Phase
