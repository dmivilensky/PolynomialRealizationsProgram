import Mathlib.Analysis.Complex.JensenFormula

/-!
Article: jacobi, Proposition 2.2.
This is the finite-zero form of Jensen's formula, valid about any point
where the entire function is nonzero. Centering there avoids assuming
that the function is nonzero at the frequency origin. The logarithmic
contribution of any finite family of distinct actual zeros is bounded
by the true boundary growth of the function.
Source: B. Ya. Levin, Distribution of Zeros of Entire Functions, Jensen's
formula; the analytic divisor and circle average are those of mathlib.
Use: each original positive and negative Bessel frequency contributes at least one to the source Jensen bound.
-/
namespace jacobi.Complex
noncomputable section
open Real Set Metric MeromorphicOn Function
open scoped Topology

/-- Every zero of a nonzero entire function has genuine positive integer multiplicity in the actual analytic divisor.
Use: each original positive and negative Bessel frequency contributes at least one to the source Jensen bound.
Article: jacobi, Proposition 2.2.
Source: the identity theorem and analytic zero multiplicity.
Proof: a nonzero entire function has finite analytic order everywhere.
At a zero that finite natural order is positive; the actual analytic
divisor on any containing domain is that same integer. -/
theorem divisor_at_zero_ge_one {f : ℂ → ℂ} (hf : ∀ z,AnalyticAt ℂ f z)
    {c u : ℂ} (hc : f c≠0) {U : Set ℂ} (hu : u∈U) (hzero : f u=0) :
    (1:ℤ)≤divisor f U u := by
  -- The identity theorem excludes an infinite order, rather than assigning a multiplicity to a locally zero function.
  have htop : analyticOrderAt f u≠⊤ := by
    intro h
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u hf).mp h
    exact hc (congrFun he c)
  obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hn0 : n≠0 := by
    intro h
    have ho := (hf u).analyticOrderAt_ne_zero.mpr hzero
    exact ho (by simpa [h] using hn.symm)
  have hU : AnalyticOnNhd ℂ f U := fun z _ => hf z
  rw [hU.divisor_apply hu,← hn]
  simpa using (show (1:ℤ)≤(n:ℤ) by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)

/-- A finite family of genuine distinct zeros contributes its full logarithmic mass to Jensen's actual circle average.
Use: the growing original Bessel zero prefix contradicts the proved small exponential type in GL injectivity.
Article: jacobi, Proposition 2.2.
Source: Levin, Distribution of Zeros of Entire Functions; mathlib Jensen formula.
Proof: apply the community Jensen identity to the actual analytic
divisor. Its logarithmic terms are nonnegative inside the disk; at the
center the logarithm is zero by totalization. Every chosen zero has
multiplicity at least one. Drop all remaining nonnegative terms. -/
theorem finite_zero_log_sum_le {f : ℂ → ℂ} (hf : ∀ z,AnalyticAt ℂ f z)
    {c : ℂ} (hc : f c≠0) {R : ℝ} (hR : 0<R) (S : Finset ℂ)
    (hS : ∀ u∈S,u∈closedBall c R ∧ f u=0) :
    ∑ u∈S,Real.log (R*‖c-u‖⁻¹)≤
      circleAverage (fun z => Real.log ‖f z‖) c R-Real.log ‖f c‖ := by
  classical
  -- Keep the complete Jensen mass; a single-radius zero count loses the constant needed in the source argument.
  let U := closedBall c R
  have hU : AnalyticOnNhd ℂ f U := fun z _ => hf z
  let D := divisor f U
  let J := fun u => (D u:ℝ)*Real.log (R*‖c-u‖⁻¹)
  have hJ (u : ℂ) : 0≤J u := by
    by_cases hu : u∈U
    · apply mul_nonneg (by exact_mod_cast hU.divisor_nonneg u)
      by_cases hcu : c=u
      · simp [hcu]
      · apply Real.log_nonneg
        apply (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hcu))).mpr
        simpa only [div_eq_mul_inv] using (show ‖c-u‖≤R from by
          simpa only [U,mem_closedBall,dist_eq_norm'] using hu)
    · simp only [J,D,Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu,
        Int.cast_zero,zero_mul,le_refl]
  have hfinite : HasFiniteSupport J :=
    (D.finiteSupport (isCompact_closedBall c R)).subset (by
      intro u hu
      change D u≠0
      intro he
      exact hu (by simp only [J,he,Int.cast_zero,zero_mul]))
  have hU' : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa only [abs_of_pos hR] using hU
  have hjensen := hU'.circleAverage_log_norm hR.ne' hc
  rw [abs_of_pos hR] at hjensen
  have hsum := Finset.sum_le_sum (s := S) (fun u hu =>
    mul_le_mul_of_nonneg_right
      (show (1:ℝ)≤D u by exact_mod_cast divisor_at_zero_ge_one hf hc (hS u hu).1 (hS u hu).2)
      (by
        have hcuz : c≠u := fun h => hc (h ▸ (hS u hu).2)
        have hu' := (hS u hu).1
        apply Real.log_nonneg
        apply (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hcuz))).mpr
        simpa only [div_eq_mul_inv] using (show ‖c-u‖≤R from by
          simpa only [mem_closedBall,dist_eq_norm'] using hu')))
  simp only [one_mul] at hsum
  have hdrop : ∑ u∈S,J u≤∑ᶠ u,J u := by
    rw [finsum_eq_sum_of_support_subset J (s := S∪hfinite.toFinset) (by
      intro u hu
      exact Finset.mem_union_right _ (hfinite.mem_toFinset.mpr hu))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (fun u _ _ => hJ u)
  have he : (∑ᶠ u,J u)=circleAverage (fun z => Real.log ‖f z‖) c R-Real.log ‖f c‖ := by
    dsimp only [J,D,U]
    linarith
  exact hsum.trans (hdrop.trans_eq he)

/-- Actual finite zero contributions of an entire function are bounded by its genuine exponential type, with the original nonzero center retained.
Use: applies the analytic Jensen theorem directly to the source reference coefficient transform and its original frequency growth bound.
Article: jacobi, Proposition 2.2.
Source: Levin, Distribution of Zeros of Entire Functions, exponential-type form of Jensen's formula.
Proof: on the actual radius-R circle about c, the frequency norm is at
most norm(c)+R. Bound the logarithm by the true exponential growth,
including zeros on the circle, and insert this circle-average bound
in the proved full finite-zero Jensen inequality. -/
theorem finite_zero_log_sum_le_exp {f : ℂ → ℂ} (hf : ∀ z,AnalyticAt ℂ f z)
    {c : ℂ} (hc : f c≠0) {C τ R : ℝ} (hC : 1≤C) (hτ : 0≤τ) (hR : 0<R)
    (hgrowth : ∀ z,‖f z‖≤C*Real.exp (τ*‖z‖)) (S : Finset ℂ)
    (hS : ∀ u∈S,u∈closedBall c R ∧ f u=0) :
    ∑ u∈S,Real.log (R*‖c-u‖⁻¹)≤
      Real.log C+τ*(‖c‖+R)-Real.log ‖f c‖ := by
  -- The center need not be zero; its fixed norm only changes the additive constant, not the source type.
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hU : AnalyticOnNhd ℂ f (closedBall c |R|) := fun z _ => hf z
  have havg : circleAverage (fun z => Real.log ‖f z‖) c R≤Real.log C+τ*(‖c‖+R) := by
    apply circleAverage_mono_on_of_le_circle
      ((hU.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
    intro z hz
    have hn : ‖z‖≤‖c‖+R := by
      have hh := norm_add_le (z-c) c
      rw [sub_add_cancel] at hh
      have he : ‖z-c‖=R := by simpa only [mem_sphere,dist_eq_norm,abs_of_pos hR] using hz
      linarith
    by_cases hfz : f z=0
    · simp only [hfz,norm_zero,Real.log_zero]
      exact add_nonneg (Real.log_nonneg hC) (mul_nonneg hτ (by positivity))
    · have hh := (hgrowth z).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hτ)) hCp.le)
      have hl := Real.log_le_log (norm_pos_iff.mpr hfz) hh
      rwa [Real.log_mul hCp.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
  exact (finite_zero_log_sum_le hf hc hR S hS).trans (sub_le_sub_right havg _)

/-- The genuine finite-zero Jensen estimate also applies to an injectively indexed finite family, without replacing its actual multiplicities or losing an endpoint zero.
Use: indexes the original positive and negative spectral roots by sign, block and original position in the GL uniqueness proof.
Article: jacobi, Proposition 2.2.
Source: finite-family form of Jensen's formula.
Proof: apply the actual finite-set theorem to the image of the finite index type. Injectivity identifies its true sum with the indexed sum. -/
theorem indexed_zero_log_sum_le_exp {ι : Type*} [Fintype ι] {f : ℂ → ℂ}
    (hf : ∀ z,AnalyticAt ℂ f z) {c : ℂ} (hc : f c≠0) {C τ R : ℝ}
    (hC : 1≤C) (hτ : 0≤τ) (hR : 0<R) (hgrowth : ∀ z,‖f z‖≤C*Real.exp (τ*‖z‖))
    (u : ι → ℂ) (hu : Function.Injective u) (hball : ∀ i,u i∈closedBall c R)
    (hzero : ∀ i,f (u i)=0) :
    ∑ i,Real.log (R*‖c-u i‖⁻¹)≤
      Real.log C+τ*(‖c‖+R)-Real.log ‖f c‖ := by
  classical
  have hh := finite_zero_log_sum_le_exp hf hc hC hτ hR hgrowth
    (Finset.univ.image u) (by
      intro z hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨hball i,hzero i⟩)
  rwa [Finset.sum_image (fun i _ j _ hij => hu hij)] at hh

end
end jacobi.Complex
