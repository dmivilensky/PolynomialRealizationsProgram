import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The leading endpoint Laplace asymptotic is proved for actual measurable
bounded coefficients, using the original convergent Euler Gamma integral.
This is the analytic endpoint lemma needed to extract the leading
coefficient from the already proved reference beta representation.
Source: the leading term of Watson's lemma for Laplace integrals.
Use: fixes the leading coefficient in laplace_endpoint_limit, hence the original negative-axis reference characteristic normalization.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Dominated convergence evaluates the actual endpoint-rescaled Laplace integral with its exact Gamma factor.
Use: fixes the leading coefficient in laplace_endpoint_limit, hence the original negative-axis reference characteristic normalization.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the leading term of Watson's lemma, proved here from Lebesgue dominated convergence and Euler's Gamma integral.
Proof: for every positive integration variable u, the coefficient
h(u/y) tends to h(0). A global bound on h supplies the integrable
majorant M*exp(-u)*u^(g-1), whose integral is the original Gamma value. -/
theorem laplace_rescaled_limit {g : ℝ} (hg : 0<g) {h : ℝ → ℝ}
    (hm : Measurable h) (hc : ContinuousAt h 0)
    (hb : ∃ M : ℝ,0≤M ∧ ∀ s,|h s|≤M) :
    Tendsto (fun y : ℝ => ∫ u : ℝ in Ioi 0,Real.exp (-u)*u^(g-1)*h (u/y))
      atTop (𝓝 (Real.Gamma g*h 0)) := by
  -- The same Euler integral controls every genuine coefficient-rescaled integrand.
  obtain ⟨M,hM,hb⟩ := hb
  have hi := Real.GammaIntegral_convergent hg
  have hmeas (y : ℝ) : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-u)*u^(g-1)*h (u/y)) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    exact ((Real.measurable_exp.comp measurable_id.neg).mul
      (measurable_id.pow_const _)).mul (hm.comp (measurable_id.div_const y))
  have hbound (y : ℝ) : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      ‖Real.exp (-u)*u^(g-1)*h (u/y)‖≤M*(Real.exp (-u)*u^(g-1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hu _)]
    exact (mul_le_mul_of_nonneg_left (hb _)
      (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hu _)).le).trans_eq (by ring)
  have hlim : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      Tendsto (fun y : ℝ => Real.exp (-u)*u^(g-1)*h (u/y)) atTop
        (𝓝 (Real.exp (-u)*u^(g-1)*h 0)) := by
    filter_upwards with u
    exact tendsto_const_nhds.mul (hc.tendsto.comp (tendsto_id.const_div_atTop u))
  have hd := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => M*(Real.exp (-u)*u^(g-1)))
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound) (hi.const_mul M) hlim
  simpa only [integral_mul_const,← Real.Gamma_eq_integral hg] using hd

/-- Positive dilation of the original Laplace integral has exactly its endpoint-rescaled form.
Use: transfers laplace_rescaled_limit to the original variable in laplace_endpoint_limit; the original integral is not redefined by its asymptotic.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: positive change of variables u=y*s in Watson's endpoint lemma.
Proof: the community half-line substitution gives the true Jacobian.
On the positive half-line, the powers y^g, y^(-1) and y^(-(g-1))
cancel exactly, leaving the original rescaled coefficient h(u/y). -/
theorem laplace_endpoint_rescale (g : ℝ) (h : ℝ → ℝ) {y : ℝ} (hy : 0<y) :
    y^g*(∫ s : ℝ in Ioi 0,Real.exp (-(y*s))*s^(g-1)*h s)=
      ∫ u : ℝ in Ioi 0,Real.exp (-u)*u^(g-1)*h (u/y) := by
  -- Substitution is applied to the original Lebesgue integral, including its genuine zero endpoint.
  let G : ℝ → ℝ := fun s => Real.exp (-(y*s))*s^(g-1)*h s
  have hs := integral_comp_mul_left_Ioi G 0 (inv_pos.mpr hy)
  simp only [mul_zero,inv_inv,smul_eq_mul] at hs
  have he : (∫ u : ℝ in Ioi 0,G (y⁻¹*u))=
      y^(-(g-1))*(∫ u : ℝ in Ioi 0,Real.exp (-u)*u^(g-1)*h (u/y)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp [G]
    rw [mul_inv_cancel_left₀ hy.ne',Real.mul_rpow (inv_pos.mpr hy).le hu.le,
      Real.inv_rpow hy.le,← Real.rpow_neg hy.le]
    rw [show y⁻¹*u=u/y by ring]
    ring
  rw [he] at hs
  have hh := congrArg (fun x : ℝ => y^(g-1)*x) hs
  have hc : y^(g-1)*y^(-(g-1))=1 := by
    rw [← Real.rpow_add hy,add_neg_cancel,Real.rpow_zero]
  have ht : y^(g-1)*y=y^g := by
    calc
      _ = y^((g-1)+1) := by rw [Real.rpow_add hy,Real.rpow_one]
      _ = _ := by congr 1; ring
  simpa only [← mul_assoc,hc,one_mul,ht] using hh.symm

/-- The genuine original endpoint Laplace integral has its exact leading Gamma coefficient.
Use: applies to the truncated continuous regular coefficient of the article's actual reference beta integral and to the Bessel Poisson integral.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the leading term of Watson's lemma, proved here from the actual positive dilation and dominated convergence.
Proof: the original integral equals its genuinely rescaled form for every positive y; this equality holds eventually at infinity, where laplace_rescaled_limit gives the stated limit. -/
theorem laplace_endpoint_limit {g : ℝ} (hg : 0<g) {h : ℝ → ℝ}
    (hm : Measurable h) (hc : ContinuousAt h 0)
    (hb : ∃ M : ℝ,0≤M ∧ ∀ s,|h s|≤M) :
    Tendsto (fun y : ℝ => y^g*(∫ s : ℝ in Ioi 0,Real.exp (-(y*s))*s^(g-1)*h s))
      atTop (𝓝 (Real.Gamma g*h 0)) := by
  apply (laplace_rescaled_limit hg hm hc hb).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  exact (laplace_endpoint_rescale g h hy).symm

end
end jacobi.Reference
