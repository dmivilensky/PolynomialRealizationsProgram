import jacobi.Jacobi.RegularCotangent

/-!
Article: jacobi, Proposition B.1.
Even analytic regular factors give an extra vanishing order in the genuine
Wronskian. The actual endpoint exponent 2*alpha+2 is positive for alpha>-1,
including the cases where the original Liouville functions diverge.
Use: gives a common exact regular-singular factorization for the Jacobi and Bessel comparison waves.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- An actual power times a regular function, with the selected positive-axis real power.
Use: gives a common exact regular-singular factorization for the Jacobi and Bessel comparison waves.
Article: jacobi, Proposition B.1.
-/
def powerFactor (p : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := x^p*g x

/-- The literal derivative expression for an actual regular-singular factorized wave.
Use: computes the actual endpoint Wronskian before taking its singular limit.
Article: jacobi, Proposition B.1.
-/
def powerFactorSlope (p : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  p*x^(p-1)*g x+x^p*deriv g x

/-- The regular-singular product derivative formula is a genuine ordinary derivative on the positive axis.
Use: identifies the exact slopes of the actual Jacobi and Bessel factorized waves.
Article: jacobi, Proposition B.1.
Proof: the positive real-power derivative and the actual regular factor derivative obey the ordinary product rule. -/
theorem powerFactor_hasDerivAt {g : ℝ → ℝ} {p x : ℝ} (hx : 0<x)
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (powerFactor p g) (powerFactorSlope p g x) x := by
  convert (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).mul hg.hasDerivAt using 1 <;> rfl

/-- The exact Wronskian of two waves with the same singular endpoint exponent factors out twice that power.
Use: the extra zero from the even analytic regular factors is separated from the possibly negative outer exponent.
Article: jacobi, Proposition B.1.
Proof: expand both literal slopes, cancel the matching leading power
terms, and combine the positive-base real powers exactly. -/
theorem powerFactor_wronskian {p x : ℝ} (hx : 0<x) (g h : ℝ → ℝ) :
    powerFactorSlope p g x*powerFactor p h x-powerFactor p g x*powerFactorSlope p h x=
      x^(2*p)*(deriv g x*h x-g x*deriv h x) := by
  rw [show 2*p=p+p by ring,Real.rpow_add hx]
  dsimp [powerFactorSlope,powerFactor]
  ring

/-- Analytic regular factors with vanishing first derivatives have a genuine zero Wronskian limit whenever the source endpoint exponent is admissible.
Use: discharges the singular boundary term in Sturm comparison for every alpha>-1 without assuming square-integrability of separate unweighted derivatives.
Article: jacobi, Proposition B.1.
Proof: the regular Wronskian numerator is differentiable at zero and
vanishes there. Its actual divided difference is continuous. Factor it
as x times that divided difference; the full Wronskian is then x^(2*p+1)
times a continuous function and 2*p+1 is strictly positive. -/
theorem powerFactor_wronskian_tendsto {p : ℝ} (hp : 0<2*p+1)
    {g h : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) (hh : AnalyticAt ℝ h 0)
    (hg0 : deriv g 0=0) (hh0 : deriv h 0=0) :
    Tendsto (fun x : ℝ => powerFactorSlope p g x*powerFactor p h x-
      powerFactor p g x*powerFactorSlope p h x) (𝓝[>] 0) (𝓝 0) := by
  -- The solutions themselves may diverge; only their exact Wronskian is passed to the endpoint limit.
  let L : ℝ → ℝ := fun x => deriv g x*h x-g x*deriv h x
  have hL : AnalyticAt ℝ L 0 := (hg.deriv.mul hh).sub (hg.mul hh.deriv)
  have hzero : L 0=0 := by simp only [L,hg0,hh0,zero_mul,mul_zero,sub_self]
  have hD : ContinuousAt (dslope L 0) 0 := continuousAt_dslope_same.mpr hL.differentiableAt
  have hr : Tendsto (fun x : ℝ => x^(2*p+1)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuous_rpow_const hp.le).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have ht := hr.mul (hD.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ) from nhdsWithin_le_nhds))
  simp only [zero_mul] at ht
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0<x at hx
  rw [powerFactor_wronskian hx g h,Real.rpow_add_one hx.ne',dslope_of_ne _ hx.ne']
  simp only [slope,vsub_eq_sub,sub_zero,hzero,smul_eq_mul]
  dsimp only [L]
  field_simp [hx.ne']

/-- Actual derivatives agree with the selected regular-singular product slope whenever the original functions agree locally.
Use: connects the singular Wronskian calculation to the actual Jacobi and Bessel slopes, rather than formal derivative placeholders.
Article: jacobi, Proposition B.1.
Proof: the actual positive-power product has its proved ordinary derivative; local equality and uniqueness identify that derivative with the original slope. -/
theorem slope_eq_powerFactor {f g : ℝ → ℝ} {p x d : ℝ} (hx : 0<x)
    (hf : HasDerivAt f d x) (hg : DifferentiableAt ℝ g x)
    (he : f=ᶠ[𝓝 x] powerFactor p g) : d=powerFactorSlope p g x :=
  hf.unique ((powerFactor_hasDerivAt hx hg).congr_of_eventuallyEq he)

/-- The actual Wronskian of two original functions tends to zero on their proved common admissible regular-singular branch.
Use: discharges the boundary hypothesis of the singular Sturm comparison for the actual finite Jacobi and Bessel waves.
Article: jacobi, Proposition B.1.
Proof: actual endpoint factorizations identify the original slopes with
the genuine power-product slopes throughout a small positive interval.
Analyticity gives the required local factor derivatives; the preceding
proved singular Wronskian limit then applies to the original functions. -/
theorem wronskian_tendsto_of_endpoint_factors {p e : ℝ} (hp : 0<2*p+1) (he : 0<e)
    {f f' G G' g h : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) (hh : AnalyticAt ℝ h 0)
    (hg0 : deriv g 0=0) (hh0 : deriv h 0=0)
    (hf : ∀ x∈Ioo 0 e,HasDerivAt f (f' x) x)
    (hG : ∀ x∈Ioo 0 e,HasDerivAt G (G' x) x)
    (hfe : ∀ x∈Ioo 0 e,f x=powerFactor p g x)
    (hGe : ∀ x∈Ioo 0 e,G x=powerFactor p h x) :
    Tendsto (fun x : ℝ => f' x*G x-f x*G' x) (𝓝[>] 0) (𝓝 0) := by
  -- The original slopes are independently proved ordinary derivatives; they are identified by uniqueness only on the actual positive interval.
  have ht := powerFactor_wronskian_tendsto hp hg hh hg0 hh0
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [Ioo_mem_nhdsGT he,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hh.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with x hx hgx hhx
  have hloc : f=ᶠ[𝓝 x] powerFactor p g := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using hfe y hy
  have hlocG : G=ᶠ[𝓝 x] powerFactor p h := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using hGe y hy
  rw [slope_eq_powerFactor hx.1 (hf x hx) hgx.differentiableAt hloc,
    slope_eq_powerFactor hx.1 (hG x hx) hhx.differentiableAt hlocG,hfe x hx,hGe x hx]

end
end jacobi.Bessel
