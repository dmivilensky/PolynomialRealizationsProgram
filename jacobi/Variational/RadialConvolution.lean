import jacobi.Variational.Tails
import chebyshev2.GroundState.ConvolutionRegularity
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
For every nonzero symmetric decreasing L1 source, the actual exponential
convolution has strictly negative derivative at each positive radius. The
source need not be continuous or bounded, and its value at zero is ignored
only as a null singleton. Reflection pairs the two half-line terms; their
unweighted positive difference is the source mass in the centered interval.
Source: reflected half-line integrals and positivity of the exponential kernel.
Use: gives a positive lower bound on a genuine centered subinterval for the strict convolution proof.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open chebyshev2.GroundState chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero integrable radial source is strictly positive at some positive radius.
Use: gives a positive lower bound on a genuine centered subinterval for the strict convolution proof.
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proof: otherwise radial evenness and nonnegativity force the source zero
outside the null singleton at zero, contradicting its strictly positive integral. -/
theorem radial_positive_point {j : ℝ → ℝ} (hn : ∀ x,0≤j x)
    (hs : SymmetricDecreasing j) (hm : 0<∫ x,j x) : ∃ a : ℝ,0<a ∧ 0<j a := by
  -- No representative value at the null origin is used to witness positive mass.
  by_contra! hz
  have hae : j=ᵐ[volume] 0 := by
    have hzero : ∀ᵐ x : ℝ,x≠0 := by simp [ae_iff]
    filter_upwards [hzero] with x hx
    have hh := hz |x| (abs_pos.mpr hx)
    rw [hs.abs_eq] at hh
    exact le_antisymm hh (hn x)
  have he : (∫ x,j x)=0 := by simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae hae
  linarith

/-- Every centered nonempty interval carries positive mass of a nonzero radial integrable source.
Use: proves that the reflected source difference has positive unweighted integral.
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proof: a positive source radius gives a positive constant lower bound on
(0,min(radius,x)); integrate it there and compare this subinterval with (-x,x). -/
theorem radial_centered_integral_pos {j : ℝ → ℝ} (hj : Integrable j) (hn : ∀ x,0≤j x)
    (hs : SymmetricDecreasing j) (hm : 0<∫ x,j x) {x : ℝ} (hx : 0<x) :
    0<∫ y in (-x)..x,j y := by
  -- Radial monotonicity supplies positivity on an interval of positive Lebesgue length.
  obtain ⟨a,ha,hja⟩ := radial_positive_point hn hs hm
  let r := min a x
  have hr : 0<r := lt_min ha hx
  have hsmall : 0<∫ y in (0:ℝ)..r,j y :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hj.intervalIntegrable
      (fun y hy => hja.trans_le (hs.decreasing hy.1 ha (hy.2.le.trans (min_le_left a x)))) hr
  rw [intervalIntegral.integral_of_le hr.le,integral_Ioc_eq_integral_Ioo] at hsmall
  have hmono : (∫ y in Ioo (0:ℝ) r,j y)≤∫ y in Ioo (-x) x,j y :=
    setIntegral_mono_set hj.integrableOn (Eventually.of_forall hn)
      (Eventually.of_forall fun y hy => ⟨by linarith [hy.1],hy.2.trans_le (min_le_right a x)⟩)
  rw [intervalIntegral.integral_of_le (by linarith : -x≤x),integral_Ioc_eq_integral_Ioo]
  exact hsmall.trans_le hmono

/-- Reflection in a real cutting point exchanges the two open half-line integrals exactly.
Use: puts both convolution-slope terms on the same half-line before comparing their sources.
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proof: the affine reflection preserves Lebesgue measure and maps the two half-lines bijectively. -/
theorem integral_reflect_halfline (f : ℝ → ℝ) (x : ℝ) :
    (∫ y in Iio x,f (2*x-y))=∫ y in Ioi x,f y := by
  have h := (volume.measurePreserving_sub_left (2*x)).setIntegral_preimage_emb
    (Homeomorph.subLeft (2*x)).measurableEmbedding f (Ioi x)
  have he : (fun y : ℝ => 2*x-y) ⁻¹' Ioi x=Iio x := by
    ext y
    change x<2*x-y ↔ y<x
    constructor <;> intro hy <;> linarith
  rwa [he] at h

/-- The nonnegative reflected source difference integrates to the source mass of the centered interval.
Use: its strictly positive integral makes every positive exponential weighting strictly positive too.
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proof: reflection sends the reflected term to the right tail; evenness
sends the left tail to the tail starting at -x. Subtract these integrable
tails by the interval-integral decomposition. -/
theorem radial_reflected_difference {j : ℝ → ℝ} (hj : Integrable j)
    (hs : SymmetricDecreasing j) {x : ℝ} (hx : 0<x) :
    (0≤ᵐ[volume.restrict (Iio x)] fun y => j y-j (2*x-y)) ∧
      (∫ y in Iio x,j y-j (2*x-y))=∫ y in (-x)..x,j y := by
  -- The origin is the only point excluded by the chosen radial source representative convention.
  have hnon : 0≤ᵐ[volume.restrict (Iio x)] fun y => j y-j (2*x-y) := by
    have hzero : ∀ᵐ y : ℝ,y≠0 := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_Iio,ae_restrict_of_ae hzero] with y hy hy0
    apply sub_nonneg.mpr
    exact hs.lower_on_interval (2*x-y) y (by
      have hh : |y|≤|2*x-y| := by grind [abs_eq_max_neg]
      exact abs_le.mp hh) hy0
  refine ⟨hnon,?_⟩
  rw [integral_sub hj.integrableOn (hj.comp_sub_left (2*x)).integrableOn,integral_reflect_halfline]
  have heven : (∫ y in Iio x,j y)=∫ y in Ioi (-x),j y := by
    rw [← integral_Iic_eq_integral_Iio]
    have hh := integral_comp_neg_Ioi (-x) j
    simp only [hs.even,neg_neg] at hh
    exact hh.symm
  rw [heven]
  exact intervalIntegral.integral_Ioi_sub_Ioi hj.integrableOn (by linarith)

/-- The actual exponential convolution slope is the negative of a single reflected-source pairing.
Use: turns the strict positive radial source difference into a strict negative actual derivative.
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proof: express both half-line Green terms with their common exponential
weight and reflect the right integral to the left. Their integrable
difference is the displayed single source pairing. -/
theorem convolutionSlope_reflected {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    convolutionSlope j x=-(∫ y in Iio x,exp (y-x)*(j y-j (2*x-y))) := by
  -- Each weighted term is genuinely integrable before they are combined.
  have hi (f : ℝ → ℝ) (hf : Integrable f) : IntegrableOn (fun y => exp (y-x)*f y) (Iio x) := by
    have hg : AEStronglyMeasurable (fun y : ℝ => exp (y-x)) (volume.restrict (Iio x)) :=
      (show Continuous (fun y : ℝ => exp (y-x)) by fun_prop).aestronglyMeasurable.restrict
    have hb : ∀ᵐ y : ℝ ∂volume.restrict (Iio x),‖exp (y-x)‖≤(1:ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      change y<x at hy
      rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      exact exp_le_one_iff.mpr (by linarith)
    exact hf.integrableOn.bdd_mul hg hb
  have hleft : leftGreen j x=∫ y in Iio x,exp (y-x)*j y := by
    rw [leftGreen,← integral_const_mul,integral_Iic_eq_integral_Iio]
    exact setIntegral_congr_fun measurableSet_Iio fun y _ => by rw [← mul_assoc,← exp_add]; congr 2; ring
  have hright : rightGreen j x=∫ y in Iio x,exp (y-x)*j (2*x-y) := by
    rw [rightGreen,← integral_const_mul,← integral_reflect_halfline]
    exact setIntegral_congr_fun measurableSet_Iio fun y _ => by rw [← mul_assoc,← exp_add]; congr 2; ring
  rw [convolutionSlope,hleft,hright,← integral_sub (hi _ (hj.comp_sub_left (2*x))) (hi j hj)]
  rw [← integral_neg]
  exact setIntegral_congr_fun measurableSet_Iio fun y _ => by ring

/-- The actual exponential convolution of every nonzero radial L1 source has strictly negative slope at every positive radius.
Use: closes the strict second-moment gradient monotonicity on the full measurable source domain.
Article: jacobi, Appendix D.1 (radial convolution and strict ground monotonicity).
Proof: the reflected source difference is nonnegative a.e. and has strictly
positive centered-mass integral. Its positive exponential weighting cannot
have zero integral, since that would force the original difference zero a.e. -/
theorem convolutionSlope_radial_neg {j : ℝ → ℝ} (hj : Integrable j) (hn : ∀ x,0≤j x)
    (hs : SymmetricDecreasing j) (hm : 0<∫ x,j x) {x : ℝ} (hx : 0<x) : convolutionSlope j x<0 := by
  -- Strict positivity comes from actual centered mass, not from strict monotonicity of the source.
  obtain ⟨hδ,hint⟩ := radial_reflected_difference hj hs hx
  have hg : AEStronglyMeasurable (fun y : ℝ => exp (y-x)) (volume.restrict (Iio x)) :=
    (show Continuous (fun y : ℝ => exp (y-x)) by fun_prop).aestronglyMeasurable.restrict
  have hb : ∀ᵐ y : ℝ ∂volume.restrict (Iio x),‖exp (y-x)‖≤(1:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change y<x at hy
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (by linarith)
  have hi : IntegrableOn (fun y => exp (y-x)*(j y-j (2*x-y))) (Iio x) :=
    (hj.sub (hj.comp_sub_left (2*x))).integrableOn.bdd_mul hg hb
  have hw : 0≤ᵐ[volume.restrict (Iio x)] fun y => exp (y-x)*(j y-j (2*x-y)) :=
    hδ.mono fun y hy => mul_nonneg (exp_pos _).le hy
  have hp : 0<∫ y in Iio x,exp (y-x)*(j y-j (2*x-y)) := by
    apply lt_of_le_of_ne (integral_nonneg_of_ae hw)
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg_ae hw hi).mp hz.symm
    have hδzero : (fun y => j y-j (2*x-y))=ᵐ[volume.restrict (Iio x)] 0 :=
      hae.mono fun y hy => (mul_eq_zero.mp hy).resolve_left (exp_ne_zero _)
    have he := integral_congr_ae hδzero
    rw [hint] at he
    have hh := radial_centered_integral_pos hj hn hs hm hx
    have hzδ : (∫ y in (-x)..x,j y)=0 := by simpa only [Pi.zero_apply,integral_zero] using he
    exact hh.ne' hzδ
  rw [convolutionSlope_reflected hj]
  exact neg_neg_of_pos hp

end
end jacobi.Variational
