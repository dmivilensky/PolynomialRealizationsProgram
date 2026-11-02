import jacobi.Variational.LaplaceDilation

/-!
Article: jacobi, Appendix D.1 (strict concentration gain).
The actual second spectral moment has a strictly positive linear gain on
1<=t<=2. The gain is obtained from a proved positive integral, for every
nonzero density, without a regularity or finite spatial moment assumption.
Source: the exponential tangent bound and the mass-preserving change of variables.
Use: identifies the strict exponential gain with the actual dilated spectral observation.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
set_option backward.isDefEq.respectTransparency false

/-- A two-coordinate change of variables for the actual mass-preserving density.
Use: identifies the strict exponential gain with the actual dilated spectral observation.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: both amplitude factors t cancel the t^(-2) Lebesgue Jacobian. -/
theorem laplacePair_scale (j : ℝ → ℝ) (a : ℝ) {t : ℝ} (ht : 0<t) :
    laplacePair (fun x => t*j (t*x)) a 1=laplacePair j a t := by
  -- The product measure and scalar action retain both physical coordinates explicitly.
  unfold laplacePair
  let F (z : ℝ × ℝ) := j z.1*j z.2*exp (-(a*|z.1-z.2|)/t)
  have he : (fun z : ℝ × ℝ => (t*j (t*z.1))*(t*j (t*z.2))*
      exp (-(a*|z.1-z.2|)/1))=fun z => t^2*F (t • z) := by
    funext z
    have hc : -(a*(t*|z.1-z.2|))/t= -(a*|z.1-z.2|) := by field_simp
    simp only [F,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,← mul_sub,
      abs_mul,abs_of_pos ht,div_one,hc]
    ring
  rw [he,integral_const_mul,
    Measure.integral_comp_smul_of_nonneg (volume.prod volume) F t (hR := ht.le)]
  simp only [Module.finrank_prod,Module.finrank_self,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 ht.ne'),one_mul]

/-- The pairing change of variables specializes to the article's actual density dilation.
Use: converts the strict exponential gain to a statement about G_2(m_t).
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: unfold the density dilation and apply the source-level change of variables. -/
theorem laplacePair_dilate (m : L1Source) (a : ℝ) {t : ℝ} (ht : 0<t) :
    laplacePair (m.dilate t ht).value a 1=laplacePair m.value a t :=
  laplacePair_scale m.value a ht

/-- At rate two and unit scale, the pairing is the actual second spectral moment.
Use: transports the strict pairing comparison to the observation in the variational problem.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the literal pairing is the already established exponential second-moment integral. -/
theorem laplacePair_second (m : L1Source) : laplacePair m.value 2 1=observe m .second := by
  convert m.secondPairing_self using 1
  unfold laplacePair secondPairing
  simp only [div_one,neg_mul]

/-- The actual second moment gains a positive multiple of t-1 under every small concentration.
Use: verifies the strict dilation hypothesis in the second-moment multiplier rule.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the tangent integral is strictly positive off the null diagonal.
For 1<=t<=2, 1-1/t>=(t-1)/2. -/
theorem second_strict_dilation (m : L1Source) (hm : 0<m.mass) :
    ∃ k : ℝ,0<k ∧ ∀ (t : ℝ) (ht : 1≤t),t≤2 →
      observe m .second+k*(t-1)≤observe (m.dilate t (by linarith)) .second := by
  -- A single actual finite integral supplies one uniform strictly positive coefficient.
  let C := laplaceGain m.value 2
  have hC : 0<C := laplaceGain_pos m.integrable m.measurable m.nonneg hm (by norm_num)
  refine ⟨C/2,by positivity,fun t ht ht2 => ?_⟩
  have ht0 : 0<t := by linarith
  have h := laplace_dilation_lower m.integrable m.measurable m.nonneg (a := 2) (by norm_num) ht0
  rw [laplacePair_second,← laplacePair_dilate m 2 ht0,laplacePair_second] at h
  have hc : (t-1)/2≤1-1/t := by
    apply (mul_le_mul_iff_of_pos_right ht0).mp
    have hid : (1/t)*t=1 := div_mul_cancel₀ _ ht0.ne'
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht2)]
  have hb := mul_le_mul_of_nonneg_right hc hC.le
  change observe m .second+C/2*(t-1)≤_
  dsimp only [C] at *
  nlinarith

end
end jacobi.Variational
