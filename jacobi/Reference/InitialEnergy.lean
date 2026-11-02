import jacobi.Reference.InitialScale
import jacobi.Reference.FrequencyEnergy

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The two proved source state bounds are evaluated at the genuine point
1/(4*pi*|omega|). Their exact normalization gives a positive uniform
bound for the actual frequency energy. The selected positive endpoint
power is retained throughout the full source order range.
Use: supplies the actual starting value for the source high-frequency energy propagation theorem.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine original reference energy at its chosen initial time has the selected endpoint-power bound uniformly in high frequency.
Use: supplies the actual starting value for the source high-frequency energy propagation theorem.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: evaluate the genuine small-scale wave and slope estimates at
the exact original initial time. Since t_0*|omega|=1/(4*pi), the slope
divided by frequency has the same selected endpoint scale as the wave.
Square both genuine estimates and add them in the actual energy. -/
theorem wave_initial_energy {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ →
      waveEnergy a omega (initialTime omega)≤C*(initialTime omega)^(2*gamma a) := by
  -- The starting state is the actual source solution, with no independent asymptotic normalization premise.
  obtain ⟨A,B,hA,hB,hsmall⟩ := wave_small_scale ha
  refine ⟨A^2+(4*Real.pi*B)^2,by positivity,fun omega homega => ?_⟩
  obtain ⟨ht,hscale⟩ := initialTime_properties homega
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hg : 0<(initialTime omega)^(gamma a) := Real.rpow_pos_of_pos ht.1 _
  obtain ⟨hu,hv⟩ := hsmall omega homega (initialTime omega) ht hscale.le
  have hv' : ‖waveSlope a omega (initialTime omega)‖/‖omega‖≤
      (4*Real.pi*B)*(initialTime omega)^(gamma a) := by
    apply (div_le_iff₀ hRp).mpr
    apply hv.trans_eq
    dsimp [initialTime]
    field_simp [Real.pi_ne_zero,hRp.ne']
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤A*(initialTime omega)^(gamma a))).mpr hu
  have hv2 := (sq_le_sq₀ (by positivity : 0≤‖waveSlope a omega (initialTime omega)‖/‖omega‖)
    (by positivity : 0≤(4*Real.pi*B)*(initialTime omega)^(gamma a))).mpr hv'
  have hpower : ((initialTime omega)^(gamma a))^2=(initialTime omega)^(2*gamma a) := by
    rw [show 2*gamma a=gamma a*2 by ring,Real.rpow_mul ht.1.le,Real.rpow_two]
  unfold waveEnergy frequencyEnergy
  rw [div_pow] at hv2
  rw [mul_pow,hpower] at hu2 hv2
  nlinarith

/-- The true selected endpoint power at the original initial time is at most the inverse-frequency power.
Use: converts the proved actual initial energy scale to the source |omega|^-gamma amplitude scale.
Article: jacobi, Lemma C.1.
Proof: the exact initial time is at most 1/|omega|, and the genuine exponent gamma is positive throughout the full source range. -/
theorem initialTime_power_bound {a : ℝ} (ha : -1<a) {omega : ℂ} (homega : 1≤‖omega‖) :
    (initialTime omega)^(gamma a)≤‖omega‖^(-gamma a) := by
  -- Compare the actual positive initial time with the reciprocal genuine frequency before applying the selected power.
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have ht : initialTime omega≤‖omega‖⁻¹ := by
    change 1/(4*Real.pi*‖omega‖)≤‖omega‖⁻¹
    rw [← one_div]
    apply one_div_le_one_div_of_le hRp
    nlinarith [Real.two_le_pi]
  have hh := Real.rpow_le_rpow (initialTime_properties homega).1.1.le ht
    (by linarith [(parameters ha).1] : 0≤gamma a)
  simpa only [← Real.rpow_neg_eq_inv_rpow] using hh

end
end jacobi.Reference
