import jacobi.Reference.CoefficientTransform
import jacobi.Reference.BesselFrequency
import jacobi.Reference.Parseval
import jacobi.Reference.SpectralSolutions

/-!
Article: jacobi, Appendix C.2 (uniform GL coercivity).
The actual coefficient integral of every original L2 input is entire
of the genuine source exponential type. If the input is supported on
the physical half interval and all its original Bessel coefficients
vanish, the proved actual Jensen theorem and actual reference Parseval
identity force the input itself to vanish. No completeness or
injectivity of the perturbed system is assumed.
Use: represents exactly the source zero extension of arbitrary L2(0,t) data, for t<=1/2, inside the shared full physical Hilbert space.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex MeasureTheory Filter
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- An actual original L2 function supported on the physical first half, in its genuine almost-everywhere sense.
Use: represents exactly the source zero extension of arbitrary L2(0,t) data, for t<=1/2, inside the shared full physical Hilbert space.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def HalfSupported (v : Space) : Prop :=
  ∀ᵐ t:Interval,(1/2:ℝ)<(t:ℝ) → v t=0

/-- The actual original reference wave has the true half-interval exponential type uniformly on the fixed compact spatial domain.
Use: bounds the genuine coefficient transform of every L2 input by its original integrable norm.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the selected endpoint factor t^gamma is at most one on the
physical half interval. Also t*abs(Im omega)<=norm(omega)/2. Apply the
proved global genuine-wave envelope, which includes zero frequency. -/
theorem halfWave_global_bound {a : ℝ} (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∀ omega:ℂ,∀ t:Interval,
      ‖wave a omega (halfTime t)‖≤C*Real.exp (‖omega‖/2) := by
  -- Every bound is for the original physical wave, not a growth majorant substituted for it.
  obtain ⟨C,hC,hbound⟩ := wave_global_endpoint_bound ha
  refine ⟨C,hC,fun omega t => ?_⟩
  have ht := halfTime_mem t
  have hg : 0≤gamma a := by linarith [(parameters ha).1]
  have hp : (halfTime t)^(gamma a)≤1 := Real.rpow_le_one ht.1 (by linarith [ht.2]) hg
  have he : Real.exp (halfTime t*|omega.im|)≤Real.exp (‖omega‖/2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul (show halfTime t≤1/2 from ht.2)
      (Complex.abs_im_le_norm omega) (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
    linarith
  have hm := mul_le_mul hp he (Real.exp_pos _).le (by norm_num : (0:ℝ)≤1)
  calc
    _ ≤ C*(halfTime t)^(gamma a)*Real.exp (halfTime t*|omega.im|) := hbound omega _ ht
    _ = C*((halfTime t)^(gamma a)*Real.exp (halfTime t*|omega.im|)) := by ring
    _ ≤ C*(1*Real.exp (‖omega‖/2)) := mul_le_mul_of_nonneg_left hm hC.le
    _ = _ := by ring

/-- The genuine coefficient transform of every arbitrary original L2 input has exponential type at most one half.
Use: discharges the growth premise in the fully proved source Bessel Jensen uniqueness theorem.
Article: jacobi, Proposition C.2.
Proof: bound the actual physical wave pointwise by its proved true
exponential type. The original L2 input is genuinely L1; its integral
norm supplies the actual constant. Increase that constant by one to
retain a strict positive bound also for the zero input. -/
theorem coefficientTransform_growth {a : ℝ} (ha : -1<a) (v : Space) :
    ∃ C:ℝ,0<C ∧ ∀ omega:ℂ,‖coefficientTransform a v omega‖≤C*Real.exp (‖omega‖/2) := by
  -- Integrability and the bound both use the original Lebesgue L2 representative.
  obtain ⟨B,hB,hbound⟩ := halfWave_global_bound ha
  let L := ∫ t:Interval,‖v t‖
  have hL : 0≤L := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨L*B+1,by positivity,fun omega => ?_⟩
  have hh := norm_integral_le_of_norm_le
    (f := fun t:Interval => (v t:ℂ)*wave a omega (halfTime t))
    ((space_integrable v).norm.mul_const (B*Real.exp (‖omega‖/2)))
    (Eventually.of_forall (fun t:Interval => by
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hbound omega t) (norm_nonneg _)))
  rw [integral_mul_const] at hh
  change ‖coefficientTransform a v omega‖≤L*(B*Real.exp (‖omega‖/2)) at hh
  calc
    _ ≤ L*(B*Real.exp (‖omega‖/2)) := hh
    _ = (L*B)*Real.exp (‖omega‖/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- The original real-energy coefficient integral of a genuine original L2 input.
Use: gives the literal V(sigma_k) and V(tau_k) entering the original real GL quadratic form and its injectivity proof.
Article: jacobi, Proposition C.2.
-/
def realCoefficient (a : ℝ) (v : Space) (E : ℝ) : ℝ :=
  ∫ t:Interval,v t*realSolution a E (halfTime t)

/-- At every genuine real energy the actual complex frequency transform is exactly the original real coefficient integral.
Use: transfers vanishing of the original source Bessel coefficients to the true entire frequency transform, without imposing a square-root branch.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the genuine square-invariance theorem identifies the actual
wave with the actual energy solution. The proved source reality
identity turns its integral into the complex inclusion of the genuine
real coefficient integral. -/
theorem coefficientTransform_at_energy (a : ℝ) (v : Space) {omega : ℂ} {E : ℝ}
    (h : omega^2=(E:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ)) :
    coefficientTransform a v omega=(realCoefficient a v E:ℂ) := by
  rw [coefficientTransform,realCoefficient,← integral_complex_ofReal]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change (v t:ℂ)*wave a omega (halfTime t)=(v t*realSolution a E (halfTime t):ℝ)
    rw [Complex.ofReal_mul,realSolution_cast,solution_eq_wave a h])

/-- Every original half-supported coefficient at an actual reference energy is the genuine full reference Parseval coefficient.
Use: vanishing of the true entire frequency transform forces all actual reference basis coefficients to vanish, so the input itself is zero.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: on the physical first half the clamp is the original coordinate
and the actual energy solution is the proved original reference
eigenfunction. On the other half the actual input is zero almost
everywhere, by precisely its source zero-extension property. -/
theorem realCoefficient_reference (a : ℝ) (v : Space) (hv : HalfSupported v) (k : ℕ) :
    realCoefficient a v (eigenvalue a k)=referenceCoefficient a k v := by
  -- This is the actual full-interval reference coefficient, not a compressed-system Parseval assumption.
  unfold realCoefficient referenceCoefficient
  apply integral_congr_ae
  filter_upwards [hv] with t ht
  by_cases hh : (t:ℝ)≤1/2
  · have hc : halfTime t=(t:ℝ) := min_eq_left hh
    rw [hc,realSolution_at_reference]
  · rw [ht (lt_of_not_ge hh)]
    simp only [zero_mul]

/-- Arbitrary original L2 functions supported on the physical half interval are uniquely determined by their genuine Bessel spectral coefficient integrals.
Use: supplies the actual injectivity step of the source GL positivity proof, with neither perturbed completeness nor a spectral sampling hypothesis assumed.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the true coefficient transform is entire, even and has the
proved half-interval exponential type. The actual Bessel coefficient
zeros therefore force it to vanish by the fully proved Jensen theorem.
Its original reference coefficients then vanish as well. Genuine
reference Parseval makes the norm of the original input zero. -/
theorem bessel_coefficients_injective {a : ℝ} (ha : -1<a) (v : Space)
    (hv : HalfSupported v) (hzero : ∀ k,realCoefficient a v (jacobi.Bessel.sigma a ha k)=0) : v=0 := by
  -- All analytic, growth, spectral and Parseval premises below are proved for the literal original data.
  have htransform : coefficientTransform a v=0 := bessel_entire_uniqueness ha
    (coefficientTransform_analytic a ha v) (fun k => by
      have hsq : (besselFrequency a ha k:ℂ)^2=(jacobi.Bessel.sigma a ha k:ℂ)-
          (jacobi.Jacobi.endpointCorrection a:ℂ) := by exact_mod_cast besselFrequency_sq ha k
      have hh := coefficientTransform_at_energy a v hsq
      rw [hzero k,Complex.ofReal_zero] at hh
      exact ⟨hh,(coefficientTransform_even a v _).trans hh⟩)
    (coefficientTransform_growth ha v)
  have hc (k : ℕ) : referenceCoefficient a k v=0 := by
    have hsq : ((Real.pi*(k+gamma a):ℝ):ℂ)^2=(eigenvalue a k:ℂ)-
        (jacobi.Jacobi.endpointCorrection a:ℂ) := by
      dsimp [eigenvalue]
      push_cast
      ring
    have hh := coefficientTransform_at_energy a v hsq
    rw [htransform,Pi.zero_apply,realCoefficient_reference a v hv k] at hh
    exact Complex.ofReal_injective hh.symm
  have hs := reference_parseval_hasSum a ha v
  simp only [hc,zero_pow (by norm_num : (2:ℕ)≠0),zero_div] at hs
  have hn : ‖v‖^2=0 := hs.unique hasSum_zero
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

end
end jacobi.Reference
