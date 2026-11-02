import jacobi.Hankel.ComplexConnectionPhase
import jacobi.Hankel.IncomingRemainder

/-!
Article: jacobi, Lemma E.1.
The uniform real-ray Hankel expansion supplies the initial bounds for
complex-frequency propagation and the numbered Bessel zero tail.
Use: uniform_bessel_realRay_hankel gives its true uniform cubic error for complex order, before propagation to the complex-frequency zero disks.
-/
namespace jacobi.Hankel
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- The actual canonically phased outgoing/incoming Hankel approximation of the original normalized Bessel Liouville function divided by its genuine outgoing coefficient.
Use: uniform_bessel_realRay_hankel gives its true uniform cubic error for complex order, before propagation to the complex-frequency zero disks.
Article: jacobi, Lemma E.1.
-/
def besselHankelApprox (a : ℂ) (x : ℝ) : ℂ :=
  realPhase Complex.I x*amplitudePolynomial (besselCoefficient a) x-
    besselZeroPhase a*realPhase (-Complex.I) x*incomingPolynomial (besselCoefficient a) x

/-- A genuine real-ray Fourier phase with purely imaginary coefficient has norm exactly one.
Use: bessel_realRay_hankel bounds the actual two-wave remainder without a spatial exponential loss on its original real ray.
Article: jacobi, Lemma E.1.
Proof: the real part of the actual phase exponent is zero; evaluate the community complex exponential norm formula. -/
theorem realPhase_norm {c : ℂ} (hc : c.re=0) (x : ℝ) : ‖realPhase c x‖=1 := by
  simp only [realPhase,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,hc,
    zero_mul,mul_zero,sub_zero,Real.exp_zero]

/-- The genuine original Bessel connection phase has a finite exponential norm bound uniform on an actual complex-order disk about a real center.
Use: uniform_bessel_realRay_hankel obtains one actual cubic remainder constant throughout that original complex disk.
Article: jacobi, Lemma E.1.
Proof: the real part of the original doubled phase exponent is -pi*Im(alpha); its imaginary coordinate differs from the real center by at most the actual complex distance. -/
theorem besselZeroPhase_bound {a : ℂ} {a0 r : ℝ} (ha : ‖a-(a0:ℂ)‖<r) :
    ‖besselZeroPhase a‖≤Real.exp (Real.pi*r) := by
  -- The original phase is bounded directly, with no separate special-function amplitude estimate.
  have hi := Complex.abs_im_le_norm (a-(a0:ℂ))
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  have he : (2*Complex.I*(Real.pi:ℂ)*(a/2+3/4)).re= -Real.pi*a.im := by
    norm_num [Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.normSq]
    ring
  rw [besselZeroPhase,Complex.norm_exp,he]
  apply Real.exp_le_exp.mpr
  have hh := (neg_le_abs a.im).trans (hi.trans ha.le)
  nlinarith [Real.pi_pos]

/-- The genuine original Bessel solution has a cubic canonically phased real-ray Hankel error whenever its independently proved actual phase and nonzero leading coefficient are supplied.
Use: uniform_bessel_realRay_hankel discharges both original coefficient facts and all contraction conditions on the genuine common complex-order disk.
Article: jacobi, Lemma E.1.
Proof: divide the exact original Bessel-Jost decomposition by the genuine nonzero outgoing coefficient, substitute the actual relative phase, and bound the two original amplitude errors by their independently proved cubic estimates. -/
theorem bessel_realRay_hankel {R : ℝ} (hR : 0<R) {a : ℂ} (ha : -1<a.re)
    (hc : ‖besselCoefficient a‖/R≤1/2)
    (hphase : incomingBesselCoefficient hR a= -besselZeroPhase a*outgoingBesselCoefficient hR a)
    (hA : outgoingBesselCoefficient hR a≠0) {x : ℝ} (hx : R<x) :
    ‖complexBesselWave a x/outgoingBesselCoefficient hR a-besselHankelApprox a x‖≤
      (1+‖besselZeroPhase a‖)*‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖/(12*x^3) := by
  -- The actual outgoing coefficient is divided only after its true nonvanishing and exact relative phase have been supplied.
  have hd : complexBesselWave a x/outgoingBesselCoefficient hR a=
      realPhase Complex.I x*besselAmplitude hR a x-
        besselZeroPhase a*realPhase (-Complex.I) x*incomingAmplitude hR a x := by
    rw [bessel_decomposition hR ha hc hx,hphase]
    field_simp
    ring
  rw [hd,show realPhase Complex.I x*besselAmplitude hR a x-
      besselZeroPhase a*realPhase (-Complex.I) x*incomingAmplitude hR a x-besselHankelApprox a x=
      realPhase Complex.I x*(besselAmplitude hR a x-amplitudePolynomial (besselCoefficient a) x)-
        besselZeroPhase a*realPhase (-Complex.I) x*
          (incomingAmplitude hR a x-incomingPolynomial (besselCoefficient a) x) by unfold besselHankelApprox; ring]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul,norm_mul,realPhase_norm (by simp : Complex.I.re=0),
    realPhase_norm (by simp : (-Complex.I).re=0),one_mul,mul_one]
  exact (add_le_add (besselAmplitude_cubic hR hc hx.le)
    (mul_le_mul_of_nonneg_left (incomingAmplitude_cubic hR hc hx.le) (norm_nonneg _))).trans_eq (by ring)

/-- The actual original Bessel function has one genuine canonically phased cubic Hankel bound for all complex orders on a common disk and all real spatial points on a common far ray.
Use: complex-frequency propagation and the original numbered-zero construction start from a uniform estimate proved for the original Bessel function, with no assumed Hankel expansion, phase, leading-amplitude or inverse-solvability certificate.
Article: jacobi, Lemma E.1.
Proof: choose the independently proved original common phase disk and nonzero outgoing coefficient. The actual contraction bounds its true polynomial residual coefficient; the genuine canonical phase is exponentially bounded by the disk radius. Combine the proved original Bessel cubic estimate with those explicit actual uniform bounds. -/
theorem uniform_bessel_realRay_hankel {a0 : ℝ} (ha0 : -1<a0) :
    ∃ R r C : ℝ,∃ hR : 0<R,0<r ∧ r<a0+1 ∧ 0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖<r →
      ‖besselCoefficient a‖/R≤1/2 ∧ -1<a.re ∧ outgoingBesselCoefficient hR a≠0 ∧
      ∀ x : ℝ,R<x → ‖complexBesselWave a x/outgoingBesselCoefficient hR a-besselHankelApprox a x‖≤C/x^3 := by
  -- Every actual coefficient and phase bound is discharged on one original common complex-order disk.
  obtain ⟨R,r,hR,hr,hra,hdata⟩ := common_bessel_connection_phase ha0
  let B : ℝ := R/2
  have hB : 0<B := half_pos hR
  let C : ℝ := (1+Real.exp (Real.pi*r))*B*(B+2)*(B+6)/12
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨R,r,C,hR,hr,hra,hC,fun a ha => ?_⟩
  obtain ⟨hc,hreal,hphase,hA⟩ := hdata a ha
  refine ⟨hc,hreal,hA,fun x hx => ?_⟩
  have hxp : 0<x := hR.trans hx
  have hn : ‖besselCoefficient a‖≤B := by
    have h := (div_le_iff₀ hR).mp hc
    dsimp [B]
    linarith
  have h2 : ‖besselCoefficient a+2‖≤B+2 := (norm_add_le _ _).trans (by norm_num; exact hn)
  have h6 : ‖besselCoefficient a+6‖≤B+6 := (norm_add_le _ _).trans (by norm_num; exact hn)
  have hp : ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖≤B*(B+2)*(B+6) := by
    rw [norm_mul,norm_mul]
    gcongr
  have he := bessel_realRay_hankel hR hreal hc hphase hA hx
  apply he.trans
  have hh : (1+‖besselZeroPhase a‖)*‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖≤
      (1+Real.exp (Real.pi*r))*(B*(B+2)*(B+6)) := by
    gcongr
    exact besselZeroPhase_bound ha
  exact (div_le_div_of_nonneg_right hh (by positivity : 0≤12*x^3)).trans_eq (by dsimp [C]; ring)

end
end jacobi.Hankel
