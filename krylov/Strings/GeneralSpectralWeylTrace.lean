import krylov.Strings.GeneralSpectralResolvent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
Article: main_krylov, apC:prop:tauber, the local high-energy comparison.
Use: obtain the sharp leading boundary trace constant from a genuinely
absolutely continuous local function.  A linear Riccati test replaces
hyperbolic functions and loses only a lower-order k/delta term.
Source: completing the square and the proved absolutely continuous FTC.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- Elementary sharp-to-leading-order local trace bound.  The assumptions
are actual local Sobolev regularity, not a supplied trace estimate. -/
theorem trace_energy_lower {f : ℝ → ℝ} {δ k : ℝ} (hδ : 0 < δ) (hk : 0 ≤ k)
    (hf : AbsolutelyContinuousOnInterval f 0 δ)
    (hdf : IntervalIntegrable (fun x ↦ (deriv f x) ^ 2) volume 0 δ) :
    k * (f 0) ^ 2 ≤
      ∫ x in (0 : ℝ)..δ, (deriv f x) ^ 2 + (k ^ 2 + k / δ) * (f x) ^ 2 := by
  let ψ : ℝ → ℝ := fun x ↦ k * (1 - x / δ)
  have hψc : ContDiff ℝ 1 ψ := by dsimp [ψ]; fun_prop
  have hψ : AbsolutelyContinuousOnInterval ψ 0 δ :=
    hψc.contDiffOn.absolutelyContinuousOnInterval
  have hψd (x : ℝ) : HasDerivAt ψ (-k / δ) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).div_const δ)).const_mul k using 1 <;> simp [ψ]; ring
  have hf2 := hf.fun_mul hf
  have hpart := hψ.integral_deriv_mul_eq_sub hf2
  have hderiv : (fun x ↦ deriv ψ x * (f x * f x) + ψ x * deriv (fun x ↦ f x * f x) x) =ᵐ[volume.restrict (uIoc (0 : ℝ) δ)]
      (fun x ↦ (-k / δ) * (f x) ^ 2 + 2 * ψ x * f x * deriv f x) := by
    filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt,
      ae_restrict_mem measurableSet_uIoc] with x hx hxδ
    have hx' : x ∈ uIcc (0 : ℝ) δ := uIoc_subset_uIcc hxδ
    have hd2 : deriv (fun u ↦ f u * f u) x = deriv f x * f x + f x * deriv f x :=
      (show HasDerivAt (fun u ↦ f u * f u) _ x from
        (hx hx').hasDerivAt.mul (hx hx').hasDerivAt).deriv
    rw [(hψd x).deriv, hd2]
    ring
  have hpart' : (∫ x in (0 : ℝ)..δ,
      (-k / δ) * (f x) ^ 2 + 2 * ψ x * f x * deriv f x) = -k * (f 0) ^ 2 := by
    rw [← intervalIntegral.integral_congr_ae_restrict hderiv]
    convert hpart using 1
    simp [ψ, hδ.ne', pow_two]
  have hleft : IntervalIntegrable (fun x ↦
      -((-k / δ) * (f x) ^ 2 + 2 * ψ x * f x * deriv f x)) volume 0 δ := by
    have hi := ((hψ.intervalIntegrable_deriv.mul_continuousOn hf2.continuousOn).add
      (hf2.intervalIntegrable_deriv.continuousOn_mul hψ.continuousOn)).neg
    exact hi.congr_ae (hderiv.mono fun x hx ↦ congrArg Neg.neg hx)
  have hright : IntervalIntegrable
      (fun x ↦ (deriv f x) ^ 2 + (k ^ 2 + k / δ) * (f x) ^ 2) volume 0 δ := by
    exact hdf.add ((hf.continuousOn.pow 2).intervalIntegrable.const_mul _)
  have hineq := intervalIntegral.integral_mono_on hδ.le hleft hright (fun x hx ↦ ?_)
  · rw [intervalIntegral.integral_neg, hpart'] at hineq
    simpa only [neg_mul, neg_neg] using hineq
  · have hψx : 0 ≤ ψ x ∧ ψ x ≤ k := by
      dsimp only [ψ]
      have hx0 := hx.1
      have hxδ := hx.2
      constructor
      · exact mul_nonneg hk (sub_nonneg.mpr ((div_le_one hδ).mpr hxδ))
      · have hd : 0 ≤ x / δ := div_nonneg hx0 hδ.le
        nlinarith
    have hs : 0 ≤ (k ^ 2 - (ψ x) ^ 2) * (f x) ^ 2 :=
      mul_nonneg (by nlinarith) (sq_nonneg _)
    apply sub_nonneg.mp
    calc
      0 ≤ (deriv f x + ψ x * f x) ^ 2 + (k ^ 2 - (ψ x) ^ 2) * (f x) ^ 2 :=
        add_nonneg (sq_nonneg _) hs
      _ = _ := by ring

/-- The same trace bound stated with a supplied actual almost-everywhere
derivative, so it applies directly to Lebesgue primitives of L² gradients. -/
theorem trace_energy_lower_of_ae_hasDerivAt {f g : ℝ → ℝ} {δ k : ℝ}
    (hδ : 0 < δ) (hk : 0 ≤ k) (hf : AbsolutelyContinuousOnInterval f 0 δ)
    (hg : IntervalIntegrable (fun x ↦ (g x) ^ 2) volume 0 δ)
    (hd : ∀ᵐ x, x ∈ uIoc (0 : ℝ) δ → HasDerivAt f (g x) x) :
    k * (f 0) ^ 2 ≤ ∫ x in (0 : ℝ)..δ, (g x) ^ 2 + (k ^ 2 + k / δ) * (f x) ^ 2 := by
  have he : deriv f =ᵐ[volume.restrict (uIoc (0 : ℝ) δ)] g := by
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_uIoc] with x hx hxδ
    exact (hx hxδ).deriv
  have hi : IntervalIntegrable (fun x ↦ (deriv f x) ^ 2) volume 0 δ :=
    hg.congr_ae (he.symm.mono fun x hx ↦ congrArg (fun r : ℝ ↦ r ^ 2) hx)
  have hh := trace_energy_lower hδ hk hf hi
  convert hh using 1
  exact intervalIntegral.integral_congr_ae_restrict
    (he.symm.mono fun x hx ↦ by dsimp only; rw [hx])

/-- The boundary trace estimate applies to the true complex Lebesgue
primitive of an L² gradient; both real coordinates are treated by FTC. -/
theorem trace_primitive_energy_lower (a : ℂ) {g : ℝ → ℂ} {δ k : ℝ}
    (hδ : 0 < δ) (hk : 0 ≤ k) (hg : IntervalIntegrable g volume 0 δ)
    (hgsq : IntervalIntegrable (fun x ↦ ‖g x‖ ^ 2) volume 0 δ) :
    k * ‖a‖ ^ 2 ≤ ∫ x in (0 : ℝ)..δ,
      ‖g x‖ ^ 2 + (k ^ 2 + k / δ) * ‖a + ∫ y in (0 : ℝ)..x, g y‖ ^ 2 := by
  have hnorm (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hgre : IntervalIntegrable (fun x ↦ (g x).re ^ 2) volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le]
    apply hgsq.1.mono'
      ((Complex.continuous_re.comp_aestronglyMeasurable hg.1.aestronglyMeasurable).pow 2)
    filter_upwards [] with x
    change ‖(g x).re ^ 2‖ ≤ ‖g x‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _), hnorm]
    nlinarith [sq_nonneg (g x).im]
  have hgim : IntervalIntegrable (fun x ↦ (g x).im ^ 2) volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le]
    apply hgsq.1.mono'
      ((Complex.continuous_im.comp_aestronglyMeasurable hg.1.aestronglyMeasurable).pow 2)
    filter_upwards [] with x
    change ‖(g x).im ^ 2‖ ≤ ‖g x‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _), hnorm]
    nlinarith [sq_nonneg (g x).re]
  have hgR : IntervalIntegrable (fun x ↦ (g x).re) volume 0 δ :=
    ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have hgI : IntervalIntegrable (fun x ↦ (g x).im) volume 0 δ :=
    ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩
  let R : ℝ → ℝ := fun x ↦ a.re + ∫ y in (0 : ℝ)..x, (g y).re
  let I : ℝ → ℝ := fun x ↦ a.im + ∫ y in (0 : ℝ)..x, (g y).im
  have hR : AbsolutelyContinuousOnInterval R 0 δ :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ a.re)).contDiffOn.absolutelyContinuousOnInterval).fun_add
      (hgR.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp))
  have hI : AbsolutelyContinuousOnInterval I 0 δ :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ a.im)).contDiffOn.absolutelyContinuousOnInterval).fun_add
      (hgI.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp))
  have hdR : ∀ᵐ x, x ∈ uIoc (0 : ℝ) δ → HasDerivAt R (g x).re x := by
    filter_upwards [hgR.ae_hasDerivAt_integral] with x hx hxδ
    exact (hx (uIoc_subset_uIcc hxδ) 0 (by simp)).const_add a.re
  have hdI : ∀ᵐ x, x ∈ uIoc (0 : ℝ) δ → HasDerivAt I (g x).im x := by
    filter_upwards [hgI.ae_hasDerivAt_integral] with x hx hxδ
    exact (hx (uIoc_subset_uIcc hxδ) 0 (by simp)).const_add a.im
  have hre := trace_energy_lower_of_ae_hasDerivAt hδ hk hR hgre hdR
  have him := trace_energy_lower_of_ae_hasDerivAt hδ hk hI hgim hdI
  have hir : IntervalIntegrable
      (fun x ↦ (g x).re ^ 2 + (k ^ 2 + k / δ) * R x ^ 2) volume 0 δ :=
    hgre.add ((hR.continuousOn.pow 2).intervalIntegrable.const_mul _)
  have hii : IntervalIntegrable
      (fun x ↦ (g x).im ^ 2 + (k ^ 2 + k / δ) * I x ^ 2) volume 0 δ :=
    hgim.add ((hI.continuousOn.pow 2).intervalIntegrable.const_mul _)
  have hsum := add_le_add hre him
  have hzero : k * R 0 ^ 2 + k * I 0 ^ 2 = k * ‖a‖ ^ 2 := by
    simp only [R, I, intervalIntegral.integral_same, add_zero, hnorm]
    ring
  rw [hzero, ← intervalIntegral.integral_add hir hii] at hsum
  convert hsum using 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) δ := by
    rw [uIcc_of_le hδ.le] at hx ⊢
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have heR : R x = (a + ∫ y in (0 : ℝ)..x, g y).re := by
    change a.re + (∫ y in (0 : ℝ)..x, (g y).re) = a.re + (∫ y in (0 : ℝ)..x, g y).re
    congr 1
    exact Complex.reCLM.intervalIntegral_comp_comm (hg.mono_set hsub)
  have heI : I x = (a + ∫ y in (0 : ℝ)..x, g y).im := by
    change a.im + (∫ y in (0 : ℝ)..x, (g y).im) = a.im + (∫ y in (0 : ℝ)..x, g y).im
    congr 1
    exact Complex.imCLM.intervalIntegral_comp_comm (hg.mono_set hsub)
  dsimp only
  rw [heR, heI, hnorm, hnorm]
  ring

end
end krylov.Strings.GeneralSpectral
