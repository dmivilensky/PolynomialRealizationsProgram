import jacobi.Analytic.ReferenceNorming

/-!
Article: jacobi, Lemma C.1.
Euler's integral approximation to Gamma converges uniformly on every
closed vertical strip with positive lower real part. The common scalar
error integral avoids taking parameter-dependent limits under an integral.
Use: compact-uniform normalized reference norms use this genuine Gamma
limit rather than an assumed complex Stirling formula.
Source: Euler's Gamma integral and its beta-integral approximants, mathlib Gamma.Beta.
-/
namespace jacobi.Analysis
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The genuine scalar Euler approximation, extended by zero outside its integration interval.
Use: gammaEuler_scalar_bound provides one parameter-independent Gamma-integral majorant.
Article: jacobi, Lemma C.1.
-/
def gammaEulerScalar (n:ℕ) : ℝ→ℝ := (Ioc 0 (n:ℝ)).indicator (fun x=>(1-x/n)^n)

/-- Every actual Euler scalar approximation lies between zero and the same exponential on the positive axis.
Use: dominates its scalar error uniformly over every complex parameter in a fixed real-part strip.
Article: jacobi, Lemma C.1.
Proof: on the actual integration interval use the community elementary binomial-exponential inequality; outside that interval the genuine indicator is zero. -/
theorem gammaEuler_scalar_bound (n:ℕ) {x:ℝ} (hx:0<x) :
    0≤gammaEulerScalar n x ∧ gammaEulerScalar n x≤exp (-x) := by
  by_cases hxn:x≤n
  · rw [gammaEulerScalar,indicator_of_mem (show x∈Ioc (0:ℝ) (n:ℝ) from ⟨hx,hxn⟩)]
    exact ⟨pow_nonneg (sub_nonneg.mpr (div_le_one_of_le₀ hxn (by positivity))) _,
      one_sub_div_pow_le_exp_neg hxn⟩
  · rw [gammaEulerScalar,indicator_of_notMem (fun h=>hxn h.2)]
    exact ⟨le_rfl,(exp_pos _).le⟩

/-- The actual scalar Euler approximants converge to the exponential at every positive integration point.
Use: gammaEuler_error_limit applies ordinary dominated convergence to a parameter-independent scalar error.
Article: jacobi, Lemma C.1.
Proof: eventually the growing integration interval contains the fixed positive point. The remaining expression is exactly the community limit (1-x/n)^n -> exp(-x). -/
theorem gammaEuler_scalar_limit {x:ℝ} (hx:0<x) :
    Tendsto (fun n:ℕ=>gammaEulerScalar n x) atTop (𝓝 (exp (-x))) := by
  apply (tendsto_congr' ?_).mpr (Real.tendsto_one_add_div_pow_exp (-x))
  filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
  rw [gammaEulerScalar,indicator_of_mem (show x∈Ioc (0:ℝ) (n:ℝ) from ⟨hx,(Nat.ceil_le.mp hn)⟩)]
  rw [neg_div,sub_eq_add_neg]

/-- One scalar integral controls the complex Gamma error on a complete positive-real-part strip.
Use: gammaEuler_error_bound converts its vanishing limit into uniform complex Gamma convergence.
Article: jacobi, Lemma C.1.
-/
def gammaEulerError (d G:ℝ) (n:ℕ) : ℝ :=
  ∫ x in Ioi (0:ℝ), |gammaEulerScalar n x-exp (-x)| *(x^(d-1)+x^(G-1))

/-- The actual common Euler error integral tends to zero for any positive lower and upper exponents.
Use: the same error bound works for every complex order in the strip and gives the exact uniform asymptotic.
Article: jacobi, Lemma C.1.
Proof: the difference of the genuine scalar approximant and exponential tends to zero pointwise. Its absolute value is bounded by twice the same exponential. The two positive Gamma integrands give a genuinely integrable common majorant. -/
theorem gammaEuler_error_limit {d G:ℝ} (hd:0<d) (hG:0<G) :
    Tendsto (gammaEulerError d G) atTop (𝓝 0) := by
  -- The majorant is independent of the complex parameter and of the original Euler index.
  let μ:=volume.restrict (Ioi (0:ℝ))
  have hi:Integrable (fun x:ℝ=>2*(exp (-x)*x^(d-1)+exp (-x)*x^(G-1))) μ:=
    ((Real.GammaIntegral_convergent hd).add (Real.GammaIntegral_convergent hG)).const_mul 2
  have hm (n:ℕ):AEStronglyMeasurable
      (fun x:ℝ=>|gammaEulerScalar n x-exp (-x)| *(x^(d-1)+x^(G-1))) μ:=by
    have hf:Measurable (gammaEulerScalar n):=(by
      dsimp [gammaEulerScalar]
      exact (by fun_prop : Measurable (fun x:ℝ=>(1-x/n)^n)).indicator measurableSet_Ioc)
    have he:Measurable (fun x:ℝ=>exp (-x)):=by fun_prop
    have hw:Measurable (fun x:ℝ=>x^(d-1)+x^(G-1)):=by fun_prop
    simpa only [Real.norm_eq_abs,Pi.mul_def,Pi.sub_apply] using ((hf.sub he).norm.mul hw).aestronglyMeasurable (μ:=μ)
  have hb (n:ℕ):∀ᵐx:ℝ∂μ,‖|gammaEulerScalar n x-exp (-x)| *(x^(d-1)+x^(G-1))‖≤
      2*(exp (-x)*x^(d-1)+exp (-x)*x^(G-1)):=by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    obtain ⟨h0,h1⟩:=gammaEuler_scalar_bound n hx
    have hd0:0≤x^(d-1):=rpow_nonneg hx.le _
    have hG0:0≤x^(G-1):=rpow_nonneg hx.le _
    rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (add_nonneg hd0 hG0)]
    rw [abs_of_nonpos (sub_nonpos.mpr h1)]
    nlinarith [mul_nonneg h0 (add_nonneg hd0 hG0),
      mul_nonneg (exp_pos (-x)).le (add_nonneg hd0 hG0)]
  have ht:∀ᵐx:ℝ∂μ,Tendsto
      (fun n:ℕ=>|gammaEulerScalar n x-exp (-x)| *(x^(d-1)+x^(G-1))) atTop (𝓝 (0:ℝ)):=by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    simpa only [sub_self,abs_zero,zero_mul] using
      (((gammaEuler_scalar_limit hx).sub_const (exp (-x))).abs.mul_const (x^(d-1)+x^(G-1)))
  have h:=tendsto_integral_of_dominated_convergence _ hm hi hb ht
  change Tendsto (fun n:ℕ=>∫ x:ℝ,|gammaEulerScalar n x-exp (-x)| *(x^(d-1)+x^(G-1)) ∂μ) atTop (𝓝 0)
  simpa only [integral_zero] using h

end
end jacobi.Analysis
