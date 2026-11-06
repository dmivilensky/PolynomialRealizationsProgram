import nesterov.Phase.Algebra
import nesterov.Phase.SingleAtom

/-!
Article: Equations (imab), (Theta) and the stable upper-semicircle phase.
Use: the original endpoint-polynomial angle has the source principal branch.
-/
namespace nesterov.Phase
noncomputable section
open Spectral Set

def momentumAngle (q : Momentum.Tuning) (μ L ω : ℝ) : ℝ :=
  angle (g ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0) (frequency ω))
    (skew ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0) (frequency ω))

/-- Strict positivity of s on the open upper semicircle, from the actual tuning. -/
theorem momentum_skew_pos (q : Momentum.Tuning) {μ L ω : ℝ} (hμL : μ<L)
    (hω : ω∈Ioo (0:ℝ) Real.pi) :
    0<skew ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0) (frequency ω) := by
  let z := polyak.Waves.z 0 (Real.arccos (frequency ω))
  have hz : Complex.normSq z=1 := by
    simpa [z] using polyak.Waves.normSq_z_pow 0 (Real.arccos (frequency ω)) 1
  have hzi : 0<z.im := by
    have hh := polyak.Waves.z_pow_im 0 (Real.arccos (frequency ω)) 1
    have hsin := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
    have him : z.im=Real.sin ω := by
      simpa [z,arccos_frequency ⟨hω.1.le,hω.2.le⟩] using hh
    rw [him]
    exact hsin
  let B := Quadratic.characteristic q.beta q.tau q.stepSize μ z*
    star (Quadratic.characteristic q.beta q.tau q.stepSize L z)
  have hB : 0<B.im := characteristic_cross_im_pos q hμL hz hzi
  let k := 4/(q.stepSize^2*(L-μ)^2)
  have hk : 0<k := div_pos (by norm_num) (mul_pos (pow_pos q.step_pos _) (pow_pos (sub_pos.mpr hμL) _))
  let a := (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L 0
  have hf : ((g a (frequency ω):ℝ):ℂ)-2*Complex.I*skew a (frequency ω)= -(k:ℂ)*B := by
    have hh := momentum_factor (β:=q.beta) (τ:=q.tau) hμL q.step_pos.ne' 0 (frequency ω)
    convert hh using 1
    dsimp [B,k,z]
    ring
  have hi : -2*skew a (frequency ω)= -k*B.im := by
    have hh := congrArg Complex.im hf
    simpa using hh
  have hp := mul_pos hk hB
  change 0<skew a (frequency ω)
  nlinarith only [hi,hp]

theorem momentumAngle_pos_lt_pi (q : Momentum.Tuning) {μ L ω : ℝ} (hμL : μ<L)
    (hω : ω∈Ioo (0:ℝ) Real.pi) : 0<momentumAngle q μ L ω ∧ momentumAngle q μ L ω<Real.pi :=
  angle_pos_lt_pi (momentum_skew_pos q hμL hω)

/-- The declared phase is the literal polar phase in Equation (Theta). -/
theorem polar_representation (g s : ℝ) :
    (g:ℂ)-2*Complex.I*s=(magnitude g s:ℂ)*Complex.exp (-(angle g s:ℝ)*Complex.I) := by
  rw [Complex.exp_mul_I]
  rw [Complex.cos_neg,Complex.sin_neg,←Complex.ofReal_cos,←Complex.ofReal_sin]
  have hr2 : (2:ℂ).re=(2:ℝ) := rfl
  have hi2 : (2:ℂ).im=0 := rfl
  apply Complex.ext
  · norm_num only [Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,
      Complex.I_re,Complex.I_im,hr2,hi2,zero_mul,mul_zero,add_zero,zero_add,sub_zero,mul_one]
    exact (magnitude_cos_angle g s).symm
  · norm_num only [Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,
      Complex.I_re,Complex.I_im,hr2,hi2,zero_mul,mul_zero,add_zero,zero_add,sub_zero,mul_one]
    nlinarith only [magnitude_sin_angle g s]

end
end nesterov.Phase
