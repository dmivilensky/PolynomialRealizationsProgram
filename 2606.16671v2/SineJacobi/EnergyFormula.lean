import «2606.16671v2».SineJacobi.EllipticDescent
import «2606.16671v2».SineJacobi.EnergyDerivativeBounds

/-!
Article: 2606.16671v2, Theorem 5.2.
A formula containing only the squared moduli and normalized elliptic integrals.
Use: `«2606.16671v2».SineJacobi.energyDensity_ellipticA` feeds
`«2606.16671v2».SineJacobi.energyWitnessValue_correct` (energy Witness Value correct).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
open Real Set
noncomputable section
set_option backward.isDefEq.respectTransparency false

/--
A formula containing only the squared moduli and normalized elliptic integrals.

Exact identity `energyDensity t = 4*((1-cos (Real.pi*t))/2)*((1+cos (Real.pi*t))/2)* ellipticA
((1-cos (Real.pi*t))/2)^2*ellipticA ((1+cos (Real.pi*t))/2)^2`.

Use: `«2606.16671v2».SineJacobi.energyWitnessValue_correct` rewrites with this identity to
establish membership in the specified domain/enclosure: `energyDensity t ∈ energyWitnessValue
ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem energyDensity_ellipticA {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    energyDensity t = 4*((1-cos (Real.pi*t))/2)*((1+cos (Real.pi*t))/2)*
      ellipticA ((1-cos (Real.pi*t))/2)^2*ellipticA ((1+cos (Real.pi*t))/2)^2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs : 0 < sin (Real.pi*t) := sin_pos_of_mem_Ioo
    ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩
  have hsh : 0 ≤ sin (Real.pi*t/2) := (sin_pos_of_mem_Ioo
    ⟨by nlinarith [pi_pos, ht.1], by nlinarith [pi_pos, ht.2]⟩).le
  have hch : 0 ≤ cos (Real.pi*t/2) := (cos_pos_of_mem_Ioo
    ⟨by nlinarith [pi_pos, ht.1], by nlinarith [pi_pos, ht.2]⟩).le
  have hm : (1-cos (Real.pi*t))/2 = sin (Real.pi*t/2)^2 := by
    have hh := cos_two_mul (Real.pi*t/2)
    rw [show 2*(Real.pi*t/2) = Real.pi*t by ring] at hh
    nlinarith [sin_sq_add_cos_sq (Real.pi*t/2)]
  have hm' : (1+cos (Real.pi*t))/2 = cos (Real.pi*t/2)^2 := by
    nlinarith [hm, sin_sq_add_cos_sq (Real.pi*t/2)]
  rw [hm, hm']
  unfold energyDensity sineDensity profileProduct sineProfile ellipticA
  rw [sqrt_sq hsh, sqrt_sq hch,
    show Real.pi*(1-t) = Real.pi-Real.pi*t by ring, sin_pi_sub,
    show (Real.pi-Real.pi*t)/2 = Real.pi/2-Real.pi*t/2 by ring, sin_pi_div_two_sub]
  simp only [mul_pow, div_pow, sq_sqrt hs.le, sq_sqrt pi_pos.le]
  have ht2 : sin (Real.pi*t) = 2*sin (Real.pi*t/2)*cos (Real.pi*t/2) := by
    rw [← sin_two_mul]; congr 1; ring
  rw [ht2]
  field_simp
  ring

end

end «2606.16671v2».SineJacobi
