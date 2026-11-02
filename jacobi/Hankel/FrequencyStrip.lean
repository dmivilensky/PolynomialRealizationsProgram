import jacobi.Hankel.FrequencyInitialSlope
import jacobi.Hankel.BesselHankelReal
import jacobi.Analysis.SecondOrderPropagation

/-!
Article: jacobi, Lemma E.1.
Use: uniform_bessel_frequency_strip supplies these bounds from the proved original Bessel expansion on a single complex-order disk.
-/
namespace jacobi.Hankel
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- The original Bessel error propagates vertically with its actual value, slope, and quartic forcing bounds, retaining a cubic remainder.
Use: uniform_bessel_frequency_strip supplies these bounds from the proved original Bessel expansion on a single complex-order disk.
Article: jacobi, Lemma E.1.
Proof: parametrize the vertical segment by x+i*t*y. The actual complex derivative chain rule gives a genuine second-order Cauchy state, whose forcing is bounded by D/x^3. The proved three-coordinate Gronwall estimate bounds its endpoint. -/
theorem frequencyError_vertical {R : ℝ} (hR : 0<R) {a : ℂ} (ha : -1<a.re)
    {B C D b : ℝ} (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (hc : ‖besselCoefficient a‖≤B)
    (hv : ∀ t : ℝ,R<t → ‖frequencyError hR a (t:ℂ)‖≤C/t^3)
    (hs : ∀ z : ℂ,1≤z.re → |z.im|≤b → ‖frequencyHankelResidual a z‖≤D/z.re^4)
    {x y : ℝ} (hx : R<x) (hx1 : 1≤x) (hy : |y|≤b) :
    ‖frequencyError hR a ((x:ℂ)+Complex.I*(y:ℂ))‖≤
      (C+((3+B)*C+D)+D)*Real.exp (b*(2+B))/x^3 ∧
      ‖frequencyErrorSlope hR a ((x:ℂ)+Complex.I*(y:ℂ))‖≤
        (C+((3+B)*C+D)+D)*Real.exp (b*(2+B))/x^3 := by
  -- The whole segment stays in the original right half-plane and the same genuine strip.
  let z (t : ℝ) : ℂ := (x:ℂ)+Complex.I*(t:ℂ)*(y:ℂ)
  have hzre (t : ℝ) : (z t).re=x := by simp [z,Complex.mul_re,Complex.mul_im]
  have hzim (t : ℝ) : (z t).im=t*y := by simp [z,Complex.mul_re,Complex.mul_im]
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx1
  have hzslit (t : ℝ) : z t∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hzre]; exact hxp))
  have hpath (t : ℝ) : HasDerivAt z (Complex.I*(y:ℂ)) t := by
    have hd : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := by
      simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one] using
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
    convert! ((hd.const_mul Complex.I).mul_const (y:ℂ)).const_add (x:ℂ) using 1
    simp only [mul_one]
  have hf (t : ℝ) (_ht : t∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s : ℝ => frequencyError hR a (z s))
        ((Complex.I*(y:ℂ))*frequencyErrorSlope hR a (z t)) t := by
    convert! (frequencyError_hasDerivAt hR a (hzslit t)).comp t (hpath t) using 1
    ring
  have hg (t : ℝ) (_ht : t∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s : ℝ => frequencyErrorSlope hR a (z s))
        ((Complex.I*(y:ℂ))*frequencyErrorCurvature hR a (z t)) t := by
    convert! (frequencyErrorSlope_hasDerivAt hR a (hzslit t)).comp t (hpath t) using 1
    ring
  have hcurv (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      ‖frequencyErrorCurvature hR a (z t)‖≤(1+B)*‖frequencyError hR a (z t)‖+D/x^3 := by
    have him : |(z t).im|≤b := by
      rw [hzim,abs_mul,abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg y) ht.2).trans hy
    have hsrc := hs (z t) (by rw [hzre]; exact hx1) him
    rw [hzre] at hsrc
    have h34 : x^3≤x^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (pow_nonneg hxp.le 3)]
    exact frequencyError_curvature_bound hR ha (Complex.slitPlane_ne_zero (hzslit t))
      (frequency_potential_bound hc (by rw [hzre]; exact hx1))
      (hsrc.trans (div_le_div_of_nonneg_left hD (pow_pos hxp 3) h34))
  have hsreal (t : ℝ) (ht : 1≤t) : ‖frequencyHankelResidual a (t:ℂ)‖≤D/t^4 :=
    hs (t:ℂ) ht (by simpa using (abs_nonneg y).trans hy)
  have hstart := frequencyError_initialSlope hR ha hB hC hD hc hv hsreal hx hx1
  have hstart0 : ‖frequencyError hR a (z 0)‖≤(C+((3+B)*C+D)+D)/x^3 := by
    simpa only [z,Complex.ofReal_zero,mul_zero,zero_mul,add_zero] using
      (hv x hx).trans (div_le_div_of_nonneg_right (by nlinarith : C≤C+((3+B)*C+D)+D) (by positivity))
  have hstart1 : ‖frequencyErrorSlope hR a (z 0)‖≤(C+((3+B)*C+D)+D)/x^3 := by
    simpa only [z,Complex.ofReal_zero,mul_zero,zero_mul,add_zero] using
      hstart.trans (div_le_div_of_nonneg_right (by linarith : (3+B)*C+D≤C+((3+B)*C+D)+D) (by positivity))
  have hbound := (jacobi.Analysis.second_order_segment_bound (K := 1+B) (D := D/x^3)
    (δ := (C+((3+B)*C+D)+D)/x^3) (by positivity) (by positivity)
    (div_le_div_of_nonneg_right (by nlinarith : D≤C+((3+B)*C+D)+D) (by positivity))
    hf hg hcurv hstart0 hstart1 (t := 1) ⟨by norm_num,le_rfl⟩)
  have hη : ‖Complex.I*(y:ℂ)‖=|y| := by rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [hη] at hbound
  have hfinal : (C+((3+B)*C+D)+D)/x^3*Real.exp (|y| * ((1+B)+1))≤
      (C+((3+B)*C+D)+D)*Real.exp (b*(2+B))/x^3 := by
    have he : |y| * ((1+B)+1)≤b*(2+B) := by nlinarith
    simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (by positivity : 0≤(C+((3+B)*C+D)+D)/x^3)
  simpa only [z,Complex.ofReal_one,mul_one] using
    And.intro (hbound.1.trans hfinal) (hbound.2.trans hfinal)

/-- The original normalized Bessel function has a uniform cubic Hankel expansion, including its frequency derivative, throughout every bounded complex-frequency strip and one common complex-order disk.
Use: the original large-index zero disks use this actual uniform expansion and derivative bound; the analytic GL construction then uses the resulting numbered complex zero tail.
Article: jacobi, Lemma E.1.
Proof: the genuine real-ray theorem supplies one common disk, a nonzero original connection coefficient and a uniform cubic value bound. Its half-contraction bounds the actual quadratic coefficient by R/2. Bound the true quartic residual explicitly, derive the genuine real initial slope, and propagate both actual Cauchy coordinates by the proved vertical Gronwall estimate. -/
theorem uniform_bessel_frequency_strip {a0 b : ℝ} (ha0 : -1<a0) :
    ∃ R r C : ℝ,∃ hR : 0<R,0<r ∧ r<a0+1 ∧ 0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖<r →
      ‖besselCoefficient a‖/R≤1/2 ∧ -1<a.re ∧ outgoingBesselCoefficient hR a≠0 ∧
      ∀ z : ℂ,max (R+1) 1≤z.re → |z.im|≤b →
        ‖frequencyError hR a z‖≤C/z.re^3 ∧ ‖frequencyErrorSlope hR a z‖≤C/z.re^3 := by
  -- The original Bessel theorem discharges every asymptotic, phase and nonvanishing input.
  obtain ⟨R,r,C,hR,hr,hra,hC,hdata⟩ := uniform_bessel_realRay_hankel ha0
  let B : ℝ := R/2
  let P : ℝ := B*(B+2)*(B+6)
  let D : ℝ := (1+Real.exp (Real.pi*r))*Real.exp b*P/8
  let S : ℝ := (C+((3+B)*C+D)+D)*Real.exp (b*(2+B))
  have hB : 0<B := half_pos hR
  have hP : 0<P := by dsimp [P]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hS : 0<S := by dsimp [S]; positivity
  refine ⟨R,r,S,hR,hr,hra,hS,fun a ha => ?_⟩
  obtain ⟨hc,hreal,hA,hvalue⟩ := hdata a ha
  have hcoef : ‖besselCoefficient a‖≤B := by
    have hh := (div_le_iff₀ hR).mp hc
    dsimp [B]
    linarith
  have h2 : ‖besselCoefficient a+2‖≤B+2 := (norm_add_le _ _).trans (by norm_num; exact hcoef)
  have h6 : ‖besselCoefficient a+6‖≤B+6 := (norm_add_le _ _).trans (by norm_num; exact hcoef)
  have hprod : ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖≤P := by
    dsimp only [P]
    rw [norm_mul,norm_mul]
    gcongr
  have hs (z : ℂ) (hz : 1≤z.re) (him : |z.im|≤b) : ‖frequencyHankelResidual a z‖≤D/z.re^4 := by
    exact (frequencyHankelResidual_bound (lt_of_lt_of_le zero_lt_one hz) le_rfl him hprod
      (besselZeroPhase_bound ha)).trans_eq (by dsimp [D]; ring)
  have hv (t : ℝ) (ht : R<t) : ‖frequencyError hR a (t:ℂ)‖≤C/t^3 := by
    rw [frequencyError_ofReal hR a (hR.trans ht)]
    exact hvalue t ht
  refine ⟨hc,hreal,hA,fun z hz him => ?_⟩
  have hzx : R<z.re := by have hh := (le_max_left (R+1) 1).trans hz; linarith
  have hz1 : 1≤z.re := (le_max_right (R+1) 1).trans hz
  have hh := frequencyError_vertical hR hreal hB.le hC.le hD.le hcoef hv hs hzx hz1 him
  have he : (z.re:ℂ)+Complex.I*(z.im:ℂ)=z := by
    simpa only [mul_comm] using Complex.re_add_im z
  simpa only [he,S] using hh

end
end jacobi.Hankel
