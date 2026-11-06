import nesterov.TwoStep.Mixed
import nesterov.TwoStep.Phase

/-! The mixed-polynomial test produces an actual one-atom feasible spectrum,
with every integer lag retained. -/
namespace nesterov.TwoStep
noncomputable section
open Spectral Phase Set

theorem wave_log_radius {r : ℝ} (hr : 0<r) (ω : ℝ) :
    polyak.Waves.z (Real.log r) ω=circle r ω := by
  unfold circle polyak.Waves.z
  rw [Complex.exp_add,←Complex.ofReal_exp,Real.exp_log hr]
  simp

 theorem mixed_test (q : Momentum.Tuning) {μ L r : ℝ} (hμL : μ<L) (hr : 0<r)
    {K : ℕ} (hK : 3≤K)
    (him : 0<(Quadratic.characteristic q.beta q.tau q.stepSize μ (circle r (2*Real.pi/K))*
      star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle r (2*Real.pi/K)))).im)
    (hH : ((1-circle 1 (2*Real.pi/K))*
      Quadratic.characteristic q.beta q.tau q.stepSize μ (circle r (2*Real.pi/K))*
      star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle r (2*Real.pi/K)))).re≤0) :
    Feasible ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r))
      (Real.log r) (singletonSpectrum (frequency (2*Real.pi/K))) 0 := by
  let ω := 2*Real.pi/K
  have hω : ω∈Ioo (0:ℝ) Real.pi := by
    simpa [ω,polyak.General.Regions.rationalAngle] using
      polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
  let a := (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r)
  let g := Spectral.g a (frequency ω)
  let s := skew a (frequency ω)
  let B := Quadratic.characteristic q.beta q.tau q.stepSize μ (circle r ω)*
    star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle r ω))
  let k := 4/(q.stepSize^2*(L-μ)^2)
  have hk : 0<k := div_pos (by norm_num) (mul_pos (sq_pos_of_pos q.step_pos) (sq_pos_of_pos (sub_pos.mpr hμL)))
  have hf : (g:ℂ)-2*Complex.I*s= -(k:ℂ)*B := by
    have hh := momentum_factor (β:=q.beta) (τ:=q.tau) hμL q.step_pos.ne' (Real.log r) (frequency ω)
    rw [arccos_frequency ⟨hω.1.le,hω.2.le⟩,wave_log_radius hr] at hh
    convert hh using 1
    dsimp [B,k,g,s,a]
    ring
  have hs : 0<s := by
    have hh := congrArg Complex.im hf
    have hi : -2*s= -k*B.im := by simpa using hh
    have hpos : 0<B.im := him
    nlinarith [mul_pos hk hpos]
  have hθ := angle_pos_lt_pi (g:=g) hs
  have hR := magnitude_pos (Or.inr hs.ne' : g≠0 ∨ s≠0)
  have he : ((1-circle 1 ω)*((g:ℂ)-2*Complex.I*s)).re=
      -k*((1-circle 1 ω)*B).re := by
    rw [hf]
    have hh : (1-circle 1 ω)*(-(k:ℂ)*B)= -(k:ℂ)*((1-circle 1 ω)*B) := by ring
    rw [hh]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
  have hdef := (complex_defect_phase g s ω).1
  have hcircle : Complex.exp ((ω:ℂ)*Complex.I)=circle 1 ω := by simp [circle,polyak.Waves.z]
  rw [hcircle,he] at hdef
  have hsign : 0≤Real.sin ((ω-2*angle g s)/2) := by
    have hH' : ((1-circle 1 ω)*B).re≤0 := by simpa only [mul_assoc] using hH
    have hleft : 0≤-k*((1-circle 1 ω)*B).re  := mul_nonneg_of_nonpos_of_nonpos (by linarith) hH'
    have hhalf : 0<Real.sin (ω/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hω.1]) (by linarith [hω.2,Real.pi_pos])
    nlinarith only [hdef,hleft,mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hR) hhalf]
  have hp : angle g s≤ω/2 := by
    by_contra hn
    have hh := Real.sin_neg_of_neg_of_neg_pi_lt
      (show (ω-2*angle g s)/2<0 by linarith) (show -Real.pi<(ω-2*angle g s)/2 by linarith [hθ.2,hω.1])
    linarith
  apply (singleton_feasible_of_phase (j:=1) (K:=K) (by simp) hK a (Real.log r) (frequency ω)
    (by simpa [ω] using arccos_frequency ⟨hω.1.le,hω.2.le⟩)
    (Or.inr hs.ne') ?_).2
  change |angle g s|≤Real.pi/K
  rw [abs_of_pos hθ.1]
  have heq : ω/2=Real.pi/K := by dsimp [ω];ring
  exact hp.trans_eq heq

end
end nesterov.TwoStep
