import jacobi.Reference.BetaRepresentation
import jacobi.Reference.HalfIntegerCharacteristics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The original selected reference function is the actual sine quotient,
including its removable frequency origin. Its genuine reference norms
have their exact sine values. Combined with the proved F=K=0 reduction,
these identities give the original special-case profiles 2*sin^2(pi*k*t).
Use: wave_half_sine evaluates the actual defining beta integral at the sine special order.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The exact integral of the original cosine frequency kernel, stated without division at zero frequency.
Use: wave_half_sine evaluates the actual defining beta integral at the sine special order.
Article: jacobi, Section 3.2 (sharp comparison at U).
Source: the fundamental theorem of calculus applied to the sine primitive.
Proof: the genuine derivative of sin((t-2*s)*omega) is
-2*omega*cos((t-2*s)*omega). Evaluate its original interval integral
at both endpoints and use oddness of sine. -/
theorem cosine_kernel_integral (omega : ℂ) (t : ℝ) :
    omega*(∫ s in (0:ℝ)..t,Complex.cos (((t-2*s:ℝ):ℂ)*omega))=
      Complex.sin ((t:ℂ)*omega) := by
  -- No nonzero-frequency assumption enters the genuine derivative or its endpoint integral.
  let G : ℝ → ℂ := fun s => Complex.sin (((t-2*s:ℝ):ℂ)*omega)
  have hd (s : ℝ) : HasDerivAt G
      ((-2*omega)*Complex.cos (((t-2*s:ℝ):ℂ)*omega)) s := by
    convert! (Complex.hasDerivAt_sin (((t-2*s:ℝ):ℂ)*omega)).comp s
      ((((hasDerivAt_id s).const_mul 2).const_sub t).ofReal_comp.mul_const omega) using 1
    push_cast
    ring
  have hc : Continuous (fun s:ℝ => (-2*omega)*Complex.cos (((t-2*s:ℝ):ℂ)*omega)) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable (μ := volume) 0 t)
  rw [intervalIntegral.integral_const_mul] at h
  dsimp [G] at h
  have h0 : ((t-2*(0:ℝ):ℝ):ℂ)*omega=(t:ℂ)*omega := by push_cast; ring
  have ht : ((t-2*t:ℝ):ℂ)*omega= -((t:ℂ)*omega) := by push_cast; ring
  rw [h0,ht,Complex.sin_neg] at h
  linear_combination -h/2

/-- The actual original reference wave at order 1/2 is the sine quotient with its exact selected-branch normalization.
Use: half_sine_eigenfunction and the actual GL special-case reduction identify the article's original normalized profiles.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: gamma=1 and the genuine beta normalization is B(1,1)=1.
Every original density power is zero, so the actual defining integral
is exactly the cosine kernel integral, including zero frequency. -/
theorem wave_half_sine (omega : ℂ) {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    omega*wave (1/2) omega t=Complex.sin ((t:ℂ)*omega) := by
  have hg : gamma (1/2)=1 := by norm_num [gamma]
  have hB : betaNormalization 1=1 := by
    rw [betaNormalization_eq (by norm_num)]
    norm_num [Real.Gamma_nat_eq_factorial]
  rw [wave_beta_integral (by norm_num) omega ht,betaWave,hg,hB]
  simp only [sub_self,Real.rpow_zero,Complex.ofReal_one,inv_one,one_mul,
    sineIntegrand,Complex.ofReal_one,one_mul]
  exact cosine_kernel_integral omega t

/-- The literal reference norm scalar at order 1/2 is exactly 1/(2*pi^2).
Use: half_sine_norming evaluates the genuine original reference integral norms before computing the normalized source profiles.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: insert gamma=1 and Gamma(1)=Gamma(2)=1 in the original printed scalar. -/
theorem half_sine_normConstant : normConstant (1/2)=1/(2*Real.pi^2) := by
  rw [normConstant,show gamma (1/2)=1 by norm_num [gamma]]
  norm_num [Real.Gamma_nat_eq_factorial,Real.rpow_two]
  ring

/-- Every genuine original reference norm at order 1/2 has the exact sine normalization.
Use: the actual source special-case profiles become 2*sin^2(pi*(k+1)*t).
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: specialize the proved original Gamma norm and use its actual
positive-argument recurrence to cancel Gamma(k+1). -/
theorem half_sine_norming (k : ℕ) :
    norming (1/2) k=1/(2*Real.pi^2*(k+1:ℝ)^2) := by
  rw [norming_formula (by norm_num),half_sine_normConstant,
    show gamma (1/2)=1 by norm_num [gamma]]
  have hΓ : Real.Gamma ((k:ℝ)+2)=((k:ℝ)+1)*Real.Gamma ((k:ℝ)+1) := by
    rw [show (k:ℝ)+2=((k:ℝ)+1)+1 by ring,Real.Gamma_add_one (by positivity : (k:ℝ)+1≠0)]
  norm_num only [mul_one] at *
  rw [hΓ]
  field_simp [(Real.Gamma_pos_of_pos (by positivity : 0<(k:ℝ)+1)).ne']

/-- The actual original reference sine eigenfunction has its literal frequency formula on the closed physical interval.
Use: the original whole-interval special-case profile is computed from genuine source functions, including both endpoint values.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: evaluate the proved actual sine wave at the true positive
reference frequency. At the remaining right endpoint both original
functions vanish, the sine by its exact integer-period identity. -/
theorem half_sine_eigenfunction (k : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    eigenfunction (1/2) k t=Real.sin (Real.pi*(k+1:ℝ)*t)/(Real.pi*(k+1:ℝ)) := by
  -- The right endpoint is obtained from the actual reference eigenfunction, independently of the open-disk Gauss representation.
  have hg : gamma (1/2)=1 := by norm_num [gamma]
  by_cases ht1 : t=1
  · subst t
    rw [(eigenfunction_properties (by norm_num : (-1:ℝ)<1/2) k).2.2]
    have hs : Real.sin (Real.pi*(k+1:ℝ))=0 := by
      rw [mul_comm]
      exact_mod_cast Real.sin_nat_mul_pi (k+1)
    simp only [mul_one,hs,zero_div]
  · have h := wave_half_sine ((Real.pi*(k+1:ℝ):ℝ):ℂ) ⟨ht.1,lt_of_le_of_ne ht.2 ht1⟩
    have he : ((Real.pi*(k+1:ℝ):ℝ):ℂ)=((Real.pi*((k:ℝ)+gamma (1/2)):ℝ):ℂ) := by rw [hg]
    rw [he,wave_at_reference] at h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re,← Complex.ofReal_mul,← Complex.ofReal_sin,hg] at hr
    apply (eq_div_iff (mul_pos Real.pi_pos (by positivity : 0<(k+1:ℝ))).ne').mpr
    have harg : t*(Real.pi*((k:ℝ)+1))=Real.pi*(k+1:ℝ)*t := by ring
    rw [harg] at hr
    linarith

end
end jacobi.Reference
