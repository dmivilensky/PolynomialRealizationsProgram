import jacobi.Reference.CharacteristicComparison
import jacobi.Reference.CharacteristicProduct
import jacobi.Reference.NormingRatios

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual spectral factors used to compare the two printed canonical
products converge genuinely. Their common negative-energy relative
product tends to one by the community dominated convergence theorem
for infinite products, with all bounds proved for the original spectra.
Use: factors the two original characteristic products in relative_characteristic_normalization without dropping an unknown constant.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Bessel-to-reference-phase normalization factors are genuinely multipliable.
Use: factors the two original characteristic products in relative_characteristic_normalization without dropping an unknown constant.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: each factor's deviation is bounded by a constant times
(k+gamma)^(-2), using the proved bounded spectral displacement and
the fixed original potential shift. That actual majorant is summable. -/
theorem bessel_phase_ratio_multipliable {a : ℝ} (ha : -1<a) :
    Multipliable (fun k : ℕ => (jacobi.Bessel.sigma a ha k:ℂ)/
      ((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)) := by
  -- Absolute convergence is established before the original normalization product is interpreted.
  obtain ⟨C,hC,herror⟩ := spectrum_error_bounded ha
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  let D := C+|jacobi.Jacobi.endpointCorrection a|
  have hs := (shifted_inverse_square_summable hg).mul_left (D/Real.pi^2)
  have hdev : Summable (fun k : ℕ => ‖(jacobi.Bessel.sigma a ha k:ℂ)/
      ((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)-1‖) := by
    apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    have hk : 0<(k:ℝ)+gamma a := by positivity
    have hden : 0<Real.pi^2*((k:ℝ)+gamma a)^2 := by positivity
    have hnum : |jacobi.Bessel.sigma a ha k-Real.pi^2*((k:ℝ)+gamma a)^2|≤D := by
      have he : jacobi.Bessel.sigma a ha k-Real.pi^2*((k:ℝ)+gamma a)^2=
          (jacobi.Bessel.sigma a ha k-eigenvalue a k)+ jacobi.Jacobi.endpointCorrection a := by
        unfold eigenvalue
        ring
      rw [he]
      dsimp [D]
      linarith [abs_add_le (jacobi.Bessel.sigma a ha k-eigenvalue a k) (jacobi.Jacobi.endpointCorrection a),herror k]
    have he : (jacobi.Bessel.sigma a ha k:ℂ)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)-1=
        (((jacobi.Bessel.sigma a ha k-Real.pi^2*((k:ℝ)+gamma a)^2)/
          (Real.pi^2*((k:ℝ)+gamma a)^2):ℝ):ℂ) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
        show (k:ℂ)+(gamma a:ℂ)≠0 by exact_mod_cast hk.ne']
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    have heq : D/Real.pi^2*(1/((k:ℝ)+gamma a)^2)*(Real.pi^2*((k:ℝ)+gamma a)^2)=D := by
      field_simp
    simpa only [heq] using hnum
  have hm := multipliable_one_add_of_summable hdev
  simpa only [add_sub_cancel] using hm

/-- The original genus-zero Bessel characteristic factors are genuinely multipliable at every complex energy.
Use: multiplies the original canonical products in relative_characteristic_normalization rather than manipulating totalized divergent products.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the already proved first spectral trace makes the actual factor perturbations absolutely summable. -/
theorem bessel_characteristic_multipliable {a : ℝ} (ha : -1<a) (z : ℂ) :
    Multipliable (fun k : ℕ => 1-z/(jacobi.Bessel.sigma a ha k:ℂ)) := by
  have hs := jacobi.Bessel.complex_spectral_summable (-z/2) (jacobi.Bessel.edgeValue_summable ha)
    (fun k => (jacobi.Bessel.edgeValue_properties ha).1 k |>.le)
  have hm := multipliable_one_add_of_summable hs
  convert! hm using 1
  funext k
  unfold jacobi.Bessel.edgeValue
  push_cast
  ring

/-- The actual negative-energy relative characteristic factors have one summable bound on their deviations from one.
Use: proves both genuine relative product convergence and its limit one in negative_relative_product_limit.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the original B5 shift gap gives sigma_k-c_0+y^2>=1 for y>=1. The numerator is the original inverse-square spectral displacement. -/
theorem negative_relative_factor_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ y : ℝ,1≤y → ∀ k : ℕ,
      ‖(((eigenvalue a k- jacobi.Bessel.sigma a ha k)/
        (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2):ℝ):ℂ)‖≤C/(k+1:ℝ)^2 := by
  obtain ⟨C,hC,herror⟩ := spectrum_error ha
  refine ⟨C,hC,fun y hy k => ?_⟩
  have hg := jacobi.Bessel.sigma_above_correction ha k
  change jacobi.Jacobi.endpointCorrection a< jacobi.Bessel.sigma a ha k at hg
  have hden : 1≤ jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2 := by
    nlinarith [sq_nonneg (y-1)]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos (lt_of_lt_of_le zero_lt_one hden),abs_sub_comm]
  exact (div_le_self (abs_nonneg _) hden).trans (herror k)

/-- The actual relative canonical product tends to one on the original shifted negative-energy path.
Use: compares with characteristic_negative_ratio and fixes the relative characteristic normalization constant exactly.
Article: jacobi, Appendix C.2 (norming ratios).
Source: mathlib's dominated convergence theorem for infinite products.
Proof: every actual factor perturbation tends to zero as its true
quadratic negative-energy denominator tends to infinity. The proved
original inverse-square displacement is a single summable majorant
for every y>=1, so the original complex product tends to one. -/
theorem negative_relative_product_limit {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => ∏' k : ℕ,(1+
      (((eigenvalue a k- jacobi.Bessel.sigma a ha k)/
        (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2):ℝ):ℂ)))
      atTop (𝓝 1) := by
  -- Every bound and pointwise limit belongs to the two original source spectra.
  obtain ⟨C,hC,hbound⟩ := negative_relative_factor_bound ha
  have hs : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  have hp (k : ℕ) : Tendsto (fun y : ℝ =>
      (((eigenvalue a k- jacobi.Bessel.sigma a ha k)/
        (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2):ℝ):ℂ)) atTop (𝓝 0) := by
    have hd : Tendsto (fun y : ℝ => jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2) atTop atTop := by
      apply tendsto_atTop.2
      intro B
      filter_upwards [eventually_ge_atTop (max 1 (B- jacobi.Bessel.sigma a ha k+ jacobi.Jacobi.endpointCorrection a))] with y hy
      have h1 : (1:ℝ)≤y := (le_max_left _ _).trans hy
      have h2 : B- jacobi.Bessel.sigma a ha k+ jacobi.Jacobi.endpointCorrection a≤y := (le_max_right _ _).trans hy
      nlinarith
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hd.const_div_atTop (eigenvalue a k- jacobi.Bessel.sigma a ha k))
    convert! hh using 1
  have hb : ∀ᶠ y : ℝ in atTop,∀ k : ℕ,
      ‖(((eigenvalue a k- jacobi.Bessel.sigma a ha k)/
        (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2):ℝ):ℂ)‖≤C/(k+1:ℝ)^2 := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    exact hbound y hy
  simpa only [add_zero,tprod_one] using tendsto_tprod_one_add_of_dominated_convergence hs hp hb

end
end jacobi.Reference
