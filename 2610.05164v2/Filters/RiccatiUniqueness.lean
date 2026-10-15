import «2610.05164v2».Filters.LinearUniqueness

/-!
Article: 2610.05164v2, Proposition 3.
The left asymptotic condition uniquely determines a locally AC Riccati solution.
Use: `«2610.05164v2».Filters.riccati_unique` feeds `«2610.05164v2».Filters.nonlinear_unique`
(nonlinear unique).
Proof chain: `«2610.05164v2».Filters.nonlinear_unique` — 2610.05164v2, Proposition 3; Actual
linear/Riccati filters, causal formulas, uniqueness and spectral observations.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The left asymptotic condition uniquely determines a locally AC Riccati solution. Global
boundedness is unnecessary for uniqueness.

Exact identity `f=g`.

Use: `«2610.05164v2».Filters.nonlinear_unique` uses this identity to establish the identity
`r=nonlinear s m`.

Article: 2610.05164v2, Proposition 3 via `«2610.05164v2».Filters.nonlinear_unique`.

Proof: The difference f-g satisfies a homogeneous linear equation with coefficient c=2+f+g.
Multiply by exp(integral c) to obtain a locally absolutely continuous function with zero
derivative almost everywhere, hence a constant. Far to the left, c is nonnegative because both
solutions tend to zero; the integrating factor is therefore bounded above there. The left
endpoint limit forces that constant to vanish, and positivity of the exponential yields f=g.
-/
theorem riccati_unique {j f g : ℝ → ℝ}
    (hf : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hg : ∀ a b, AbsolutelyContinuousOnInterval g a b)
    (hfd : ∀ᵐ x, HasDerivAt f (j x-2*f x-(f x)^2) x)
    (hgd : ∀ᵐ x, HasDerivAt g (j x-2*g x-(g x)^2) x)
    (hfl : Tendsto f atBot (𝓝 0)) (hgl : Tendsto g atBot (𝓝 0)) : f=g := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  -- Subtracting the two Riccati equations cancels the common forcing and factors the quadratic
  -- difference.
  let c : ℝ → ℝ := fun x => 2+f x+g x
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous c := (continuous_const.add (locallyAC_continuous hf)).add (locallyAC_continuous hg)
  let A : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, c t
  have hAd (x : ℝ) : HasDerivAt A (c x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hAc : ContDiff ℝ 1 A := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hAd x).differentiableAt,?_⟩
    have he : deriv A=c := funext (fun x => (hAd x).deriv)
    rw [he]
    exact hc
  -- The integrating factor cancels the remaining linear coefficient in the difference
  -- equation.
  let F : ℝ → ℝ := fun x => exp (A x)*(f x-g x)
  have hFac (a b : ℝ) : AbsolutelyContinuousOnInterval F a b :=
    ((contDiff_exp.comp hAc).contDiffOn : ContDiffOn ℝ 1 (fun x => exp (A x))
      (uIcc a b)).absolutelyContinuousOnInterval.mul ((hf a b).sub (hg a b))
  have hFd : ∀ᵐ x, HasDerivAt F 0 x := by
    filter_upwards [hfd,hgd] with x hx hy
    have he := ((hasDerivAt_exp (A x)).comp x (hAd x)).mul (hx.sub hy)
    change HasDerivAt F (exp (A x)*c x*(f x-g x)+
      exp (A x)*((j x-2*f x-(f x)^2)-(j x-2*g x-(g x)^2))) x at he
    convert he using 1
    dsimp [c]
    ring
  -- Local absolute continuity upgrades the almost-everywhere zero derivative to an actual
  -- constant function.
  have hF (x : ℝ) : F x=F 0 := by
    have he := locallyAC_integral_eq_sub hFac hFd 0 x
    simp only [intervalIntegral.integral_zero] at he
    linarith
  -- Record the convergence hcl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hcl : Tendsto c atBot (𝓝 2) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)) atBot (𝓝 2)).add hfl).add hgl
  have hce : ∀ᶠ x in atBot, 0 ≤ c x :=
    (hcl.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 2))).mono (fun _ hx => hx.le)
  obtain ⟨b,hb⟩ := eventually_atBot.mp hce
  -- Only a far-left upper bound on the integrating factor is needed; global boundedness of f
  -- and g is unnecessary.
  have hAb {x : ℝ} (hx : x ≤ b) : A x ≤ A b := by
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x b)
    have hn : 0 ≤ ∫ t in x..b, c t := intervalIntegral.integral_nonneg hx
      (fun t ht => hb t ht.2)
    change (∫ t in (0:ℝ)..x, c t) ≤ ∫ t in (0:ℝ)..b, c t
    linarith
  -- Compare the constant with the vanishing difference at the left asymptotic endpoint.
  have hle : ∀ᶠ x in atBot, |F 0| ≤ exp (A b)*|f x-g x| := by
    filter_upwards [eventually_le_atBot b] with x hx
    rw [← hF x]
    change |exp (A x)*(f x-g x)| ≤ _
    rw [abs_mul,abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (hAb hx)) (abs_nonneg _)
  -- Record the convergence hlim with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlim : Tendsto (fun x => exp (A b)*|f x-g x|) atBot (𝓝 0) := by
    simpa only [sub_self,abs_zero,mul_zero] using (hfl.sub hgl).abs.const_mul (exp (A b))
  have hz : F 0=0 := abs_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hle) (abs_nonneg _))
  funext x
  have he : exp (A x)*(f x-g x)=0 := (hF x).trans hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (exp_ne_zero _))

end
end «2610.05164v2».Filters
