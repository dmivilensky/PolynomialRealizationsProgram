import jacobi.Analytic.ReferenceScaledBounds
import jacobi.Analytic.ReferenceEquation
import jacobi.Reference.InitialEnergy

/-!
Article: jacobi, Lemma C.1.
The original complex-order wave and its actual slope have common
initial-scale bounds. At the genuine starting time these give exactly
the endpoint-power scale of the actual quadratic reference energy.
Use: controls both components of the initial reference state.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual complex sine prefactor has the original endpoint power bound on the whole physical half interval.
Use: controls both components of the initial reference state.
Article: jacobi, Lemma C.1.
Proof: its exact complex norm is the positive real-part power of the
physical sine base, which is at most the physical coordinate. -/
theorem weight_half_bound {a : ℂ} (ha : 0<(gamma a).re) {t : ℝ} (ht : t∈Ioc 0 (1/2)) :
    ‖weight a t‖≤t^(gamma a).re := by
  rw [weight_norm ha ⟨ht.1.le,by linarith [ht.2]⟩]
  apply Real.rpow_le_rpow (sineBase_nonneg ⟨ht.1.le,by linarith [ht.2]⟩) _ ha.le
  exact (div_le_iff₀ Real.pi_pos).mpr (by
    simpa only [mul_comm] using Real.sin_le (mul_nonneg Real.pi_pos.le ht.1.le))

/-- Both actual complex-order reference state coordinates satisfy uniform bounds throughout the original initial frequency scale.
Use: supplies the genuine starting energy for the full-half-interval complex-order estimate.
Article: jacobi, Lemma C.1.
Proof: apply the genuine uniform core and core-derivative bounds at the
original physical coordinate. The sine prefactor is at most t^(Re gamma),
its logarithmic slope is at most a fixed multiple of 1/t, and the true
coordinate slope is at most pi squared times t/2. The initial-scale
condition absorbs the remaining frequency-square factor. -/
theorem wave_small_scale {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C D : ℝ,0<C ∧ 0<D ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ → ∀ t∈Ioc (0:ℝ) (1/2),
        Real.pi*‖omega‖*t≤1/4 → ‖wave a omega t‖≤C*t^(gamma a).re ∧
          ‖waveSlope a omega t‖≤D*t^(gamma a).re/t := by
  -- Every state coordinate is the actual original function or its already proved derivative.
  obtain ⟨C,hC,hcore⟩ := waveCore_scaled_bound hG hδ
  obtain ⟨D,hD,hderiv⟩ := waveCore_scaled_deriv_bound hG hδ
  let B : ℝ := G*Real.pi/2
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨C,B*C+Real.pi^2*D/2,hC,by positivity,fun a omega hag ha hc homega t ht hsmall => ?_⟩
  have htp : 0<t := ht.1
  have hx := small_scale_coordinate ht.1 hsmall
  have hH := hcore a omega ha hc homega (coordinate t:ℂ) (by linarith)
  have hH' := hderiv a omega ha hc homega (coordinate t:ℂ) hx
  have hw := weight_half_bound hag ht
  have htgp := Real.rpow_pos_of_pos ht.1 (gamma a).re
  have hlog : ‖weightLogSlope a t‖≤B/t := weightLogSlope_uniform_bound hG ha ht
  constructor
  · rw [wave,norm_mul]
    exact (mul_le_mul hw hH (norm_nonneg _) htgp.le).trans_eq (by ring)
  · have hs : ‖waveSlope a omega t‖≤‖weight a t‖*
        (‖weightLogSlope a t‖*‖waveCore a omega (coordinate t:ℂ)‖+
          |coordinateSlope t| * ‖deriv (waveCore a omega) (coordinate t:ℂ)‖) := by
      rw [waveSlope,norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hh := norm_add_le (weightLogSlope a t*waveCore a omega (coordinate t:ℂ))
        ((coordinateSlope t:ℂ)*deriv (waveCore a omega) (coordinate t:ℂ))
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using hh
    have hs' : ‖waveSlope a omega t‖≤t^(gamma a).re*
        ((B/t)*C+(Real.pi^2*t/2)*(D*‖omega‖^2)) := by
      apply hs.trans
      apply mul_le_mul hw _ (by positivity) htgp.le
      exact add_le_add (mul_le_mul hlog hH (norm_nonneg _) (by positivity))
        (mul_le_mul (coordinateSlope_half_bound ht) hH' (norm_nonneg _) (by positivity))
    have hrt : ‖omega‖*t≤1 := by
      nlinarith [Real.two_le_pi,mul_nonneg (norm_nonneg omega) ht.1.le]
    have hrtsq : (‖omega‖*t)^2≤1 := by nlinarith [mul_nonneg (norm_nonneg omega) ht.1.le]
    have hbracket : (B/t)*C+(Real.pi^2*t/2)*(D*‖omega‖^2)≤(B*C+Real.pi^2*D/2)/t := by
      apply (le_div_iff₀ ht.1).mpr
      have he : ((B/t)*C+(Real.pi^2*t/2)*(D*‖omega‖^2))*t=
          B*C+(Real.pi^2*D/2)*(‖omega‖*t)^2 := by field_simp [ht.1.ne']
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hrtsq (show 0≤Real.pi^2*D/2 by positivity)]
    exact hs'.trans ((mul_le_mul_of_nonneg_left hbracket htgp.le).trans_eq (by ring))

/-- The genuine initial-time power is bounded by the inverse frequency power for every positive real endpoint exponent.
Use: converts the actual complex-order initial energy to the required large-frequency scale.
Article: jacobi, Lemma C.1.
Proof: the actual initial time is at most the reciprocal frequency,
and a nonnegative real power preserves this inequality. -/
theorem initialTime_power_bound {g : ℝ} (hg : 0<g) {omega : ℂ} (homega : 1≤‖omega‖) :
    (initialTime omega)^g≤‖omega‖^(-g) := by
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have ht : initialTime omega≤‖omega‖⁻¹ := by
    change 1/(4*Real.pi*‖omega‖)≤‖omega‖⁻¹
    rw [← one_div]
    apply one_div_le_one_div_of_le hRp
    nlinarith [Real.two_le_pi]
  simpa only [← Real.rpow_neg_eq_inv_rpow] using
    Real.rpow_le_rpow (initialTime_properties homega).1.1.le ht hg.le

end
end jacobi.ComplexReference
