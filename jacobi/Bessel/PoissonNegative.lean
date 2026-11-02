import jacobi.Bessel.Poisson
import jacobi.Reference.PositiveIntegral
import jacobi.Reference.TruncatedLaplace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The original Poisson integral is specialized to imaginary frequency.
Its actual endpoint Laplace limit gives the exact Bessel leading
constant throughout the Poisson order range alpha>-1/2.
Source: Poisson's integral and Watson's leading endpoint lemma, both
proved here for the original functions and Lebesgue integrals.
Use: transfers poisson_cosh_leading to the original Bessel function in normalized_negative_leading_poisson.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized Bessel function on the negative spectral axis has its exact real Poisson--cosh integral.
Use: transfers poisson_cosh_leading to the original Bessel function in normalized_negative_leading_poisson.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Poisson's Bessel integral, DLMF 10.9.4, proved here in Poisson.
Proof: specialize the genuine complex-frequency integral to i*y,
use the proved original imaginary cosine identity and the actual
real Gamma inclusions, then cancel the positive original beta scalar. -/
theorem poisson_negative_integral {a : ℝ} (ha : -(1/2:ℝ)<a) (y : ℝ) :
    (normalized (a:ℂ) ((-y^2:ℝ):ℂ)).re=
      (2*Real.Gamma (a+1)/(Real.sqrt Real.pi*Real.Gamma (a+1/2)))*
        (∫ s in (0:ℝ)..1,(1-s^2)^(a-1/2)*Real.cosh (y*s)) := by
  -- The original integral and the original normalized entire Bessel function retain their exact shared scalar.
  have hp := poisson_integral ha (Complex.I*(y:ℂ))
  have hi : (∫ s in (0:ℝ)..1,(((1-s^2)^(a-1/2):ℝ):ℂ)*Complex.cos ((Complex.I*(y:ℂ))*(s:ℂ)))=
      ((∫ s in (0:ℝ)..1,(1-s^2)^(a-1/2)*Real.cosh (y*s):ℝ):ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [mul_comm (Complex.I*(y:ℂ)),jacobi.Reference.cosine_imaginary,
      mul_comm s y,Complex.ofReal_mul]
  have hβ : Complex.Gamma (1/2:ℂ)*Complex.Gamma ((a:ℂ)+1/2)/Complex.Gamma ((a:ℂ)+1)=
      ((Real.sqrt Real.pi*Real.Gamma (a+1/2)/Real.Gamma (a+1):ℝ):ℂ) := by
    rw [Complex.ofReal_div,Complex.ofReal_mul,← Complex.Gamma_ofReal,← Complex.Gamma_ofReal]
    push_cast
    rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,Complex.Gamma_ofReal,Real.Gamma_one_half_eq]
  rw [hi,hβ,show (Complex.I*(y:ℂ))^2=((-y^2:ℝ):ℂ) by push_cast; rw [mul_pow,Complex.I_sq]; ring] at hp
  have he := congrArg Complex.re hp
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,zero_mul,mul_zero,sub_zero] at he
  have hG := (Real.Gamma_pos_of_pos (show 0<a+1/2 by linarith)).ne'
  have hH := (Real.Gamma_pos_of_pos (show 0<a+1 by linarith)).ne'
  have hπ := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he' : (2*(∫ s in (0:ℝ)..1,(1-s^2)^(a-1/2)*Real.cosh (y*s)))*Real.Gamma (a+1)=
      (Real.sqrt Real.pi*Real.Gamma (a+1/2))*(normalized (a:ℂ) ((-y^2:ℝ):ℂ)).re := by
    apply (eq_div_iff hH).mp
    rw [← div_mul_eq_mul_div]
    exact he
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hπ hG)).mpr
  linear_combination -he'

/-- The original Poisson--cosh integral has its exact leading endpoint Gamma coefficient.
Use: proves normalized_negative_leading_poisson for the same actual Bessel function whose zeros define sigma_k.
Article: jacobi, Appendix C.2 (norming ratios).
Source: Watson's leading endpoint lemma, proved here in TruncatedLaplace.
Proof: reflect the positive exponential term about one. Its endpoint
density is s^(alpha-1/2)*(2-s)^(alpha-1/2), whose regular coefficient
is bounded and continuous on [0,1]. The negative exponential term
is bounded by the genuine integral of the original Poisson weight;
after multiplying by exp(-y), every fixed power tends to zero. -/
theorem poisson_cosh_leading {a : ℝ} (ha : -(1/2:ℝ)<a) :
    Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*
      (∫ s in (0:ℝ)..1,(1-s^2)^(a-1/2)*Real.cosh (y*s)))
      atTop (𝓝 (Real.Gamma (a+1/2)*(2:ℝ)^(a-1/2)/2)) := by
  -- Watson's hypotheses are discharged for the actual regular coefficient of the reflected original Poisson density.
  let W : ℝ → ℝ := fun s => (1-s^2)^(a-1/2)
  let h : ℝ → ℝ := fun s => (2-s)^(a-1/2)
  have hW := poisson_weight_integrable ha
  have hcI : ContinuousOn h (Icc (0:ℝ) 1) := by
    intro s hs
    exact ((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (show (2:ℝ)-s≠0 by linarith [hs.2]))).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcI
  have hb : ∃ M : ℝ,0≤M ∧ ∀ s∈Icc (0:ℝ) 1,|h s|≤M := by
    refine ⟨max M 0,le_max_right _ _,fun s hs => ?_⟩
    have hv : |h s|≤M := by simpa only [Real.norm_eq_abs] using hM s hs
    exact hv.trans (le_max_left _ _)
  have hc : ContinuousAt h 0 := by
    exact (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))
  have hm : Measurable h := by dsimp [h]; fun_prop
  have hmain := jacobi.Reference.truncated_laplace_limit (g := a+1/2) (A := 1)
    (by linarith) (by norm_num) hm hc hb
  simp only [h,sub_zero,show a+1/2-1=a-1/2 by ring] at hmain
  let C := ∫ s in (0:ℝ)..1,W s
  have htail : Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*
      (∫ s in (0:ℝ)..1,W s*Real.exp (-(y*s)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      (by simpa only [one_mul,neg_mul,mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a+1/2) 1 (by norm_num)).const_mul C)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have hi : ‖∫ s in (0:ℝ)..1,W s*Real.exp (-(y*s))‖≤C := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ hW
      filter_upwards with s hs
      have hs0 : 0<s := hs.1
      have hW0 : 0≤W s := Real.rpow_nonneg (by nlinarith [hs.2]) _
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hW0,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right hW0 (Real.exp_le_one_iff.mpr (by nlinarith))
    rw [norm_mul,Real.norm_eq_abs,abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hy _),abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)
  have hsum := (hmain.add htail).div_const 2
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards with y
  have hP : IntervalIntegrable (fun s : ℝ => W s*Real.exp (y*s)) volume 0 1 :=
    hW.mul_continuousOn (by fun_prop)
  have hN : IntervalIntegrable (fun s : ℝ => W s*Real.exp (-(y*s))) volume 0 1 :=
    hW.mul_continuousOn (by fun_prop)
  have hsplit : (∫ s in (0:ℝ)..1,W s*Real.cosh (y*s))=
      ((∫ s in (0:ℝ)..1,W s*Real.exp (y*s))+(∫ s in (0:ℝ)..1,W s*Real.exp (-(y*s))))/2 := by
    rw [← intervalIntegral.integral_add hP hN,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [Real.cosh_eq]
    ring
  have hreverse : Real.exp (-y)*(∫ s in (0:ℝ)..1,W s*Real.exp (y*s))=
      ∫ s in (0:ℝ)..1,Real.exp (-(y*s))*s^(a-1/2)*(2-s)^(a-1/2) := by
    have href := intervalIntegral.integral_comp_sub_left
      (f := fun s : ℝ => Real.exp (-y)*(W s*Real.exp (y*s))) (a := 0) (b := 1) 1
    norm_num only [sub_self,sub_zero] at href
    rw [← intervalIntegral.integral_const_mul,← href]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro s hs
    dsimp only [W]
    rw [show 1-(1-s)^2=s*(2-s) by ring,
      Real.mul_rpow hs.1.le (by linarith [hs.2])]
    have he : Real.exp (-y)*Real.exp (y*(1-s))=Real.exp (-(y*s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linear_combination (s^(a-1/2)*(2-s)^(a-1/2))*he
  rw [hsplit]
  have he := congrArg (fun v : ℝ => y^(a+1/2)*v) hreverse
  linear_combination -he/2

end
end jacobi.Bessel
