import jacobi.Reference.FrequencyEnergy
import jacobi.Reference.PotentialBounds

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The actual complex-frequency energy satisfies its sharp differential
inequality. An explicit positive integrating factor removes the true
inverse-square potential bound, so propagation has a constant independent
of the large real frequency and exactly the source imaginary-frequency
exponential growth.
Use: substitutes the actual source equation into the sharp complex quadratic energy estimate.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The true reference acceleration is its genuine singular-potential frequency equation after removing the fixed spectral shift.
Use: substitutes the actual source equation into the sharp complex quadratic energy estimate.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: rearrange the already proved original reference equation and expand the exact fixed potential shift. -/
theorem waveAcceleration_frequency {a : ℝ} (ha : -1<a) (omega : ℂ)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    waveAcceleration a omega t=((singularPotential a t:ℂ)-omega^2)*wave a omega t := by
  have hh := wave_equation ha omega ht
  unfold singularPotential
  push_cast
  linear_combination -hh

/-- The actual reference wave energy has the source sharp imaginary-frequency differential bound throughout the true physical interior.
Use: propagates the genuine initial state without a growing real-frequency exponential loss.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: use the independently proved actual energy derivative, replace its true acceleration by the source equation, and apply the proved exact quadratic cancellation inequality. -/
theorem waveEnergy_deriv_le {a : ℝ} (ha : -1<a) {omega : ℂ} (homega : 0<‖omega‖)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    deriv (waveEnergy a omega) t≤
      (2*|omega.im|+|singularPotential a t|/‖omega‖)*waveEnergy a omega t := by
  rw [(waveEnergy_hasDerivAt a omega ht).deriv,waveAcceleration_frequency ha omega ht]
  exact frequencyEnergy_algebra homega (singularPotential a t)

/-- The explicit positive integrating factor applied to the genuine reference wave energy.
Use: cancels its true inverse-square potential growth on the source half interval.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def dampedWaveEnergy (a : ℝ) (omega : ℂ) (A t : ℝ) : ℝ :=
  Real.exp (-2*|omega.im| *t+A/(‖omega‖*t))*waveEnergy a omega t

/-- The genuine damped reference energy has the exact ordinary derivative of its actual integrating-factor product.
Use: proves monotonicity of the actual source energy rather than assuming a Gronwall bound.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: differentiate the actual exponential, the positive-axis reciprocal
and the original reference energy. Exact quotient algebra gives the
inverse-square correction A/(|omega| *t^2). -/
theorem dampedWaveEnergy_hasDerivAt (a : ℝ) {omega : ℂ} (homega : 0<‖omega‖)
    (A : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (dampedWaveEnergy a omega A)
      (Real.exp (-2*|omega.im| *t+A/(‖omega‖*t))*
        (deriv (waveEnergy a omega) t-
          (2*|omega.im|+A/(‖omega‖*t^2))*waveEnergy a omega t)) t := by
  -- The original energy derivative is known from the genuine reference state derivatives.
  have he := (waveEnergy_hasDerivAt a omega ht).differentiableAt.hasDerivAt
  have hl : HasDerivAt (fun s:ℝ => -2*|omega.im| *s) (-2*|omega.im|) t := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul (-2*|omega.im|)
  have hq : HasDerivAt (fun s:ℝ => A/(‖omega‖*s)) (-A/(‖omega‖*t^2)) t := by
    convert (hasDerivAt_const t A).div ((hasDerivAt_id t).const_mul ‖omega‖)
      (mul_ne_zero homega.ne' ht.1.ne') using 1
    · rfl
    · simp only [id_eq]
      field_simp [homega.ne',ht.1.ne']
      ring
  convert ((hl.add hq).exp).mul he using 1
  · rfl
  · simp only [Pi.add_apply]
    ring

/-- The genuine reference integrating-factor energy decreases on the whole source half interval with one frequency-independent inverse-square coefficient.
Use: turns the actual selected small-scale reference state into a uniform high-frequency amplitude bound.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: choose the proved actual inverse-square potential bound A/t^2.
The true reference energy is nonnegative, so that bound makes the
computed damped derivative nonpositive. The community derivative
monotonicity theorem applies on the genuine convex half interval. -/
theorem dampedWaveEnergy_antitone {a : ℝ} (ha : -1<a) :
    ∃ A : ℝ,0<A ∧ ∀ omega:ℂ,0<‖omega‖ →
      AntitoneOn (dampedWaveEnergy a omega A) (Ioc (0:ℝ) (1/2)) := by
  -- The potential coefficient depends only on the actual original order.
  obtain ⟨A,hA,hpotential⟩ := singularPotential_bound a
  refine ⟨A,hA,fun omega homega => ?_⟩
  have hderiv (t : ℝ) (ht : t∈Ioc (0:ℝ) (1/2)) : deriv (dampedWaveEnergy a omega A) t≤0 := by
    have hti : t∈Ioo 0 1 := ⟨ht.1,by linarith [ht.2]⟩
    rw [(dampedWaveEnergy_hasDerivAt a homega A hti).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hE := frequencyEnergy_nonneg omega (wave a omega t) (waveSlope a omega t)
    have hc : |singularPotential a t|/‖omega‖≤A/(‖omega‖*t^2) := by
      convert div_le_div_of_nonneg_right (hpotential t ht) homega.le using 1
      ring
    have hm := mul_le_mul_of_nonneg_right hc hE
    have hh := waveEnergy_deriv_le ha homega hti
    change 0≤waveEnergy a omega t at hE
    nlinarith
  apply antitoneOn_of_deriv_nonpos (convex_Ioc (0:ℝ) (1/2))
  · intro t ht
    exact (dampedWaveEnergy_hasDerivAt a homega A ⟨ht.1,by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  · intro t ht
    have ht' := interior_subset ht
    exact (dampedWaveEnergy_hasDerivAt a homega A ⟨ht'.1,by linarith [ht'.2]⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    exact hderiv t (interior_subset ht)

/-- The actual source reference energy propagates from any positive half-interval point with precisely the imaginary-frequency exponential and explicit inverse-square correction.
Use: supplies the full high-frequency energy estimate from the genuine initial state at t_0=1/(4*pi*|omega|).
Article: jacobi, Lemma C.1.
Proof: compare the proved decreasing damped energies at the two actual
physical points. Divide by the positive final exponential and combine
the genuine exponential factors exactly. -/
theorem waveEnergy_propagation {a : ℝ} (ha : -1<a) :
    ∃ A : ℝ,0<A ∧ ∀ omega:ℂ,0<‖omega‖ →
      ∀ s∈Ioc (0:ℝ) (1/2),∀ t∈Ioc (0:ℝ) (1/2),s≤t →
        waveEnergy a omega t≤waveEnergy a omega s*
          Real.exp (2*|omega.im| *(t-s)+A/(‖omega‖*s)-A/(‖omega‖*t)) := by
  -- The starting value is always the actual original reference energy, not a proposed asymptotic coefficient.
  obtain ⟨A,hA,hmono⟩ := dampedWaveEnergy_antitone ha
  refine ⟨A,hA,fun omega homega s hs t ht hst => ?_⟩
  have hh := hmono omega homega hs ht hst
  unfold dampedWaveEnergy at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (Real.exp_pos (2*|omega.im| *t-A/(‖omega‖*t))).le
  have he : Real.exp (2*|omega.im| *t-A/(‖omega‖*t))*
      Real.exp (-2*|omega.im| *t+A/(‖omega‖*t))=1 := by
    rw [← Real.exp_add,show (2*|omega.im| *t-A/(‖omega‖*t))+(-2*|omega.im| *t+A/(‖omega‖*t))=0 by ring,Real.exp_zero]
  rw [← mul_assoc,he,one_mul] at hm
  apply hm.trans_eq
  rw [← mul_assoc,← Real.exp_add]
  rw [show (2*|omega.im| * t-A/(‖omega‖*t))+(-2*|omega.im| * s+A/(‖omega‖*s))=
    2*|omega.im| *(t-s)+A/(‖omega‖*s)-A/(‖omega‖*t) by ring,mul_comm]

end
end jacobi.Reference
