import «2610.05164v2».Filters.LinearLimits

/-!
Article: 2610.05164v2, Proposition 3; Theorem 3.3.
`«2610.05164v2».Filters.causal_unique` proves the unique bounded causal solution of the linear
filter equation.
Use: it supplies the uniqueness clause for the integral solution
`«2610.05164v2».Filters.nonlinear_linearization`; the common-measure construction of
`«2610.05164v2».HalfLine.commonMeasure_linear_filter` uses that actual linear filter.
Source: mathlib scalar derivative calculus — integrating-factor uniqueness.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The left endpoint condition uniquely determines the locally AC linear filter. Boundedness is
unnecessary for this stronger uniqueness statement.

Exact identity `f=causal c j`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 3; Theorem 3.3.

Source: mathlib scalar derivative calculus — integrating-factor uniqueness.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem causal_unique {c : ℝ} (hc : 0 < c) {j f : ℝ → ℝ} (hj : Integrable j)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f (j x-c*f x) x) (hb : Tendsto f atBot (𝓝 0)) : f=causal c j := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let F : ℝ → ℝ := fun x => exp (c*x)*(f x-causal c j x)
  have hfac (a b : ℝ) : AbsolutelyContinuousOnInterval F a b :=
    (((contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn :
      ContDiffOn ℝ 1 (fun x : ℝ => exp (c*x)) (uIcc a b)).absolutelyContinuousOnInterval).mul
      ((hac a b).sub (causal_locallyAC hc.le hj a b))
  have hfd : ∀ᵐ x, HasDerivAt F 0 x := by
    filter_upwards [hd,causal_derivative_ae hc.le hj] with x hf hg
    have he := (hasDerivAt_exp (c*x)).comp x ((hasDerivAt_id x).const_mul c)
    have hp := he.mul (hf.sub hg)
    change HasDerivAt F
      ((exp (c*x)*(c*1))*(f x-causal c j x)+exp (c*x)*((j x-c*f x)-(j x-c*causal c j x))) x at hp
    convert hp using 1
    ring
  have he (x : ℝ) : F x=F 0 := by
    have h := locallyAC_integral_eq_sub hfac hfd 0 x
    simp only [intervalIntegral.integral_zero] at h
    linarith
  -- Record the convergence hlim with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlim : Tendsto F atBot (𝓝 0) := by
    have hex := tendsto_exp_atBot.comp (tendsto_const_nhds.pos_mul_atBot hc tendsto_id)
    change Tendsto (fun x => exp (c*x)*(f x-causal c j x)) atBot (𝓝 0)
    simpa only [Function.comp_apply,id_eq,sub_self,mul_zero] using
      hex.mul (hb.sub (causal_tendsto_atBot hc.le hj))
  have hz : F 0=0 := by
    -- Record the convergence hconst with its source filter and target limit before taking
    -- limits in the subsequent identities/bounds.
    have hconst : Tendsto F atBot (𝓝 (F 0)) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall (fun x => (he x).symm)
    exact tendsto_nhds_unique hconst hlim
  funext x
  have hx : exp (c*x)*(f x-causal c j x)=0 := (he x).trans hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (exp_ne_zero _))

end
end «2610.05164v2».Filters
