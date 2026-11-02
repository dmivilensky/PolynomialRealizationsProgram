import jacobi.Analytic.ReferenceEnergy

/-!
Article: jacobi, Lemma C.1.
An explicit integrating factor propagates the actual complex-order
reference energy with constants uniform on a bounded order set. Its
frequency dependence retains exactly the original imaginary-frequency
exponential and the integrable inverse-square potential correction.
Use: propagates the genuine initial state without a growing real-frequency exponential loss.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set jacobi.Reference
open scoped Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual reference wave energy has the source sharp imaginary-frequency differential bound throughout the true physical interior.
Use: propagates the genuine initial state without a growing real-frequency exponential loss.
Article: jacobi, Lemma C.1.
Proof: use the independently proved actual energy derivative, replace its true acceleration by the source equation, and apply the proved exact quadratic cancellation inequality. -/
theorem waveEnergy_deriv_le {a : ℂ} (ha : 0<(gamma a).re) {omega : ℂ} (homega : 0<‖omega‖)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    deriv (waveEnergy a omega) t≤
      (2*|omega.im|+‖singularPotential a t‖/‖omega‖)*waveEnergy a omega t := by
  rw [(waveEnergy_hasDerivAt a omega ht).deriv,waveAcceleration_frequency ha omega ht]
  exact frequencyEnergy_algebra homega (singularPotential a t)

/-- The explicit positive integrating factor applied to the genuine reference wave energy.
Use: cancels its true inverse-square potential growth on the source half interval.
Article: jacobi, Lemma C.1.
-/
def dampedWaveEnergy (a : ℂ) (omega : ℂ) (A t : ℝ) : ℝ :=
  Real.exp (-2*|omega.im| *t+A/(‖omega‖*t))*waveEnergy a omega t

/-- The genuine damped reference energy has the exact ordinary derivative of its actual integrating-factor product.
Use: proves monotonicity of the actual source energy rather than assuming a Gronwall bound.
Article: jacobi, Lemma C.1.
Proof: differentiate the actual exponential, the positive-axis reciprocal
and the original reference energy. Exact quotient algebra gives the
inverse-square correction A/(|omega| *t^2). -/
theorem dampedWaveEnergy_hasDerivAt (a : ℂ) {omega : ℂ} (homega : 0<‖omega‖)
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

/-- The same genuine damped energy decreases for every order in a fixed bounded complex-order set.
Use: supplies a frequency-independent propagation constant on the entire GL order disk.
Article: jacobi, Lemma C.1.
Proof: the actual complex potential has the common inverse-square bound.
The computed true energy derivative is therefore nonpositive after
multiplication by the explicit integrating factor. Apply ordinary
derivative monotonicity on the original convex half interval. -/
theorem dampedWaveEnergy_antitone {G : ℝ} (hG : 0<G) :
    ∃ A : ℝ,0<A ∧ ∀ a : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      ∀ omega : ℂ,0<‖omega‖ →
        AntitoneOn (dampedWaveEnergy a omega A) (Ioc (0:ℝ) (1/2)) := by
  -- The coefficient is independent of both moving complex parameters.
  let A : ℝ := G*(G+1)*Real.pi^2/4+1
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨A,hA,fun a ha haG omega homega => ?_⟩
  have hpotential (t : ℝ) (ht : t∈Ioc (0:ℝ) (1/2)) : ‖singularPotential a t‖≤A/t^2 :=
    (singularPotential_uniform_bound hG haG ht).trans
      (div_le_div_of_nonneg_right (by dsimp [A]; linarith) (sq_nonneg t))
  have hderiv (t : ℝ) (ht : t∈Ioc (0:ℝ) (1/2)) : deriv (dampedWaveEnergy a omega A) t≤0 := by
    have hti : t∈Ioo 0 1 := ⟨ht.1,by linarith [ht.2]⟩
    rw [(dampedWaveEnergy_hasDerivAt a homega A hti).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hE := frequencyEnergy_nonneg omega (wave a omega t) (waveSlope a omega t)
    have hc : ‖singularPotential a t‖/‖omega‖≤A/(‖omega‖*t^2) := by
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

/-- The original complex-order reference energy propagates uniformly from every actual positive half-interval point with the exact required imaginary-frequency exponential.
Use: turns the proved initial-scale values into actual full-half-interval
complex-order bounds for the GL reference functions.
Article: jacobi, Lemma C.1.
Proof: compare the proved decreasing damped energies at the two physical
points. Divide by the actual positive final integrating factor and
combine its two exponential factors exactly. -/
theorem waveEnergy_propagation {G : ℝ} (hG : 0<G) :
    ∃ A : ℝ,0<A ∧ ∀ a : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      ∀ omega : ℂ,0<‖omega‖ → ∀ s∈Ioc (0:ℝ) (1/2),∀ t∈Ioc (0:ℝ) (1/2),s≤t →
        waveEnergy a omega t≤waveEnergy a omega s*
          Real.exp (2*|omega.im| *(t-s)+A/(‖omega‖*s)-A/(‖omega‖*t)) := by
  -- The initial energy belongs to the actual original reference solution at its true physical point.
  obtain ⟨A,hA,hmono⟩ := dampedWaveEnergy_antitone hG
  refine ⟨A,hA,fun a ha haG omega homega s hs t ht hst => ?_⟩
  have hh := hmono a ha haG omega homega hs ht hst
  unfold dampedWaveEnergy at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (Real.exp_pos (2*|omega.im| *t-A/(‖omega‖*t))).le
  have he : Real.exp (2*|omega.im| *t-A/(‖omega‖*t))*
      Real.exp (-2*|omega.im| *t+A/(‖omega‖*t))=1 := by
    rw [← Real.exp_add,show (2*|omega.im| *t-A/(‖omega‖*t))+(-2*|omega.im| *t+A/(‖omega‖*t))=0 by ring,Real.exp_zero]
  rw [← mul_assoc,he,one_mul] at hm
  apply hm.trans_eq
  rw [← mul_assoc,← Real.exp_add]
  rw [show (2*|omega.im| *t-A/(‖omega‖*t))+(-2*|omega.im| *s+A/(‖omega‖*s))=
    2*|omega.im| *(t-s)+A/(‖omega‖*s)-A/(‖omega‖*t) by ring,mul_comm]

end
end jacobi.ComplexReference
