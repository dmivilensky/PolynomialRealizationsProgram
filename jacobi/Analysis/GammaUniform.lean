import jacobi.Analysis.GammaEulerUniform

/-!
Article: jacobi, Lemma C.1.
One actual scalar error integral bounds Euler's Gamma approximation for
every complex parameter in a common positive-real-part strip. Thus the
complex approximation is uniform, including its phase, rather than merely
a two-sided bound for its norm.
Use: compact-uniform reference norm asymptotics reduce their literal Gamma
quotient to this exact uniform limit.
Source: Euler's integral and dominated convergence, mathlib Gamma.Beta.
-/
namespace jacobi.Analysis
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual complex Euler integral integrand, including its original finite-interval cutoff.
Use: gammaEuler_integral identifies its genuine integral with the community GammaSeq.
Article: jacobi, Lemma C.1.
-/
def gammaEulerIntegrand (n:ℕ) (s:ℂ) : ℝ→ℂ :=
  (Ioc 0 (n:ℝ)).indicator (fun x=>((1-x/n)^n:ℝ)*(x:ℂ)^(s-1))

/-- The finite Euler integrand equals the genuine scalar cutoff times its unchanged complex power.
Use: gammaEuler_error_bound factors its exact complex difference into a scalar error and a uniformly bounded power.
Article: jacobi, Lemma C.1.
Proof: both expressions have exactly the same original integration interval and vanish off it. -/
theorem gammaEulerIntegrand_factor (n:ℕ) (s:ℂ) (x:ℝ) :
    gammaEulerIntegrand n s x=(gammaEulerScalar n x:ℂ)*(x:ℂ)^(s-1) := by
  by_cases hx:x∈Ioc (0:ℝ) (n:ℝ) <;> simp [gammaEulerIntegrand,gammaEulerScalar,hx]

/-- The actual complex Euler approximants are genuinely integrable on the positive half-line.
Use: their difference with the actual Gamma integrand has an ordinary integral, so no totalized integral is used in the uniform error estimate.
Article: jacobi, Lemma C.1.
Proof: reduce the indicator to its original finite interval. The complex power has integrable endpoint exponent Re(s)-1>-1, and its scalar polynomial factor is continuous. -/
theorem gammaEuler_integrable (n:ℕ) {s:ℂ} (hs:0<s.re) :
    Integrable (gammaEulerIntegrand n s) (volume.restrict (Ioi (0:ℝ))) := by
  -- The genuine finite interval includes the potentially singular zero endpoint only as a null boundary.
  rw [gammaEulerIntegrand,integrable_indicator_iff measurableSet_Ioc,IntegrableOn,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,← IntegrableOn,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0:ℝ)≤n)]
  apply IntervalIntegrable.continuousOn_mul
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    rwa [Complex.sub_re,Complex.one_re,← zero_sub,sub_lt_sub_iff_right]
  · fun_prop

/-- The true finite Euler integral is exactly the community Gamma approximation at every positive original index.
Use: gammaEuler_error_bound estimates the actual GammaSeq, preserving its complex phase and all normalization constants.
Article: jacobi, Lemma C.1.
Proof: rewrite the proved community finite Euler integral and the actual cutoff integral on the positive half-line; the cutoff interval is contained there. -/
theorem gammaEuler_integral {s:ℂ} (hs:0<s.re) {n:ℕ} (hn:n≠0) :
    (∫ x in Ioi (0:ℝ),gammaEulerIntegrand n s x)=Complex.GammaSeq s n := by
  rw [gammaEulerIntegrand,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
    Complex.GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤n)]

/-- The norm of the actual complex power has one common two-power majorant on a full real-part strip.
Use: gammaEuler_error_bound separates complex parameter dependence from its common scalar integration error.
Article: jacobi, Lemma C.1.
Proof: on x<=1 the lower real exponent dominates; on x>=1 the upper exponent dominates. Both powers are nonnegative on the genuine positive integration axis. -/
theorem gamma_power_strip_bound {x d G:ℝ} (hx:0<x) {s:ℂ} (hd:d≤s.re) (hG:s.re≤G) :
    ‖(x:ℂ)^(s-1)‖≤x^(d-1)+x^(G-1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.sub_re,Complex.one_re]
  by_cases hx1:x≤1
  · exact (rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans
      (le_add_of_nonneg_right (rpow_nonneg hx.le _))
  · exact (rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1)) (by linarith)).trans
      (le_add_of_nonneg_left (rpow_nonneg hx.le _))

/-- The actual scalar common error integrand is integrable for every Euler index and positive strip endpoints.
Use: gammaEuler_error_bound legitimately compares genuine integrals of norms.
Article: jacobi, Lemma C.1.
Proof: the true scalar Euler cutoff lies between zero and exp(-x). Its error times the two endpoint powers is bounded by the sum of two convergent positive Gamma integrands. -/
theorem gammaEuler_error_integrable {d G:ℝ} (hd:0<d) (hG:0<G) (n:ℕ) :
    Integrable (fun x:ℝ=>|gammaEulerScalar n x-exp (-x)| *(x^(d-1)+x^(G-1)))
      (volume.restrict (Ioi (0:ℝ))) := by
  -- Every bound concerns the unchanged original cutoff, including the empty n=0 interval.
  have hf:Measurable (gammaEulerScalar n):=(by
    dsimp [gammaEulerScalar]
    exact (by fun_prop : Measurable (fun x:ℝ=>(1-x/n)^n)).indicator measurableSet_Ioc)
  have he:Measurable (fun x:ℝ=>exp (-x)):=by fun_prop
  have hw:Measurable (fun x:ℝ=>x^(d-1)+x^(G-1)):=by fun_prop
  have hm:AEStronglyMeasurable (fun x:ℝ=>|gammaEulerScalar n x-exp (-x)| *(x^(d-1)+x^(G-1)))
      (volume.restrict (Ioi (0:ℝ))):=by
    simpa only [Real.norm_eq_abs,Pi.mul_def,Pi.sub_apply] using ((hf.sub he).norm.mul hw).aestronglyMeasurable (μ:=volume.restrict (Ioi (0:ℝ)))
  apply ((Real.GammaIntegral_convergent hd).add (Real.GammaIntegral_convergent hG)).mono' hm
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  obtain ⟨h0,h1⟩:=gammaEuler_scalar_bound n hx
  have hd0:0≤x^(d-1):=rpow_nonneg hx.le _
  have hG0:0≤x^(G-1):=rpow_nonneg hx.le _
  rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (add_nonneg hd0 hG0),
    abs_of_nonpos (sub_nonpos.mpr h1)]
  simp only [Pi.add_apply]
  nlinarith [mul_nonneg h0 (add_nonneg hd0 hG0)]

/-- The genuine complex Euler Gamma error is bounded by one scalar integral uniformly on an entire positive-real-part strip.
Use: gammaSeq_uniform_strip proves actual uniform convergence including the complex phase.
Article: jacobi, Lemma C.1.
Proof: both actual complex integrands are integrable. Subtract them under their genuine integrals, take the norm inside, and factor the difference into its exact real scalar error and complex power. Its norm has the proved common two-power strip bound. -/
theorem gammaEuler_error_bound {d G:ℝ} (hd:0<d) (hG:0<G) {s:ℂ}
    (hds:d≤s.re) (hsG:s.re≤G) {n:ℕ} (hn:n≠0) :
    ‖Complex.GammaSeq s n-Complex.Gamma s‖≤gammaEulerError d G n := by
  -- The bound estimates the actual complex functions before any Gamma quotient or normalization is introduced.
  have hs:0<s.re:=hd.trans_le hds
  have hf:=gammaEuler_integrable n hs
  have hg:=Complex.GammaIntegral_convergent hs
  rw [← gammaEuler_integral hs hn,Complex.Gamma_eq_integral hs,Complex.GammaIntegral,← integral_sub hf hg]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hf.sub hg).norm (gammaEuler_error_integrable hd hG n)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  simp only [Pi.sub_apply]
  rw [gammaEulerIntegrand_factor,← sub_mul,← Complex.ofReal_sub,norm_mul,
    Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (gamma_power_strip_bound hx hds hsG) (abs_nonneg _)

/-- Euler's actual complex Gamma sequence converges uniformly on every complete strip with a positive lower real-part bound.
Use: supplies the exact compact-uniform complex Gamma input to the printed reference norm asymptotic, rather than only magnitude bounds.
Article: jacobi, Lemma C.1.
Proof: the original complex error is bounded by one scalar error integral independently of the parameter. Its dominated-convergence limit is zero; discard only the original empty Euler index. -/
theorem gammaSeq_uniform_strip {d G:ℝ} (hd:0<d) (hG:0<G) :
    TendstoUniformlyOn (fun n:ℕ=>fun s:ℂ=>Complex.GammaSeq s n) Complex.Gamma atTop
      {s:ℂ | d≤s.re ∧ s.re≤G} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [(gammaEuler_error_limit hd hG).eventually (Iio_mem_nhds he),
    eventually_ge_atTop (1:ℕ)] with n hn hnp s hs
  rw [dist_comm,dist_eq_norm]
  exact (gammaEuler_error_bound hd hG hs.1 hs.2 (show n≠0 by omega)).trans_lt hn

end
end jacobi.Analysis
