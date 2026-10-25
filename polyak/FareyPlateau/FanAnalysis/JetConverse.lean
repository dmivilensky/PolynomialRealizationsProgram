import polyak.FareyPlateau.FanAnalysis.JetCalculus

/-! A finite quadratic quotient limit identifies the actual zero jets of an
analytic function. This is used to transfer the explicit fan calculations to
a single jointly analytic ambient family. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

theorem quadratic_limit_zero_jets {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f 0)
    (ha : Tendsto (fun δ => f δ/δ^2) (𝓝[≠] 0) (𝓝 a)) :
    f 0=0 ∧ deriv f 0=0 ∧ deriv^[2] f 0/2=a := by
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hn : ∀ᶠ δ : ℝ in 𝓝[≠] 0, δ≠0 := self_mem_nhdsWithin
  have hzero : Tendsto f (𝓝[≠] 0) (𝓝 0) := by
    have hh := (hid.pow 2).mul ha
    simp only [zero_pow (by norm_num : (2 : ℕ)≠0),zero_mul] at hh
    apply hh.congr'
    filter_upwards [hn] with δ hδ
    field_simp
  have hfzero : f 0=0 := tendsto_nhds_unique
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hzero
  have hslope : Tendsto (fun δ => f δ/δ) (𝓝[≠] 0) (𝓝 0) := by
    have hh := hid.mul ha
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [hn] with δ hδ
    field_simp
  have hfirst := hf.differentiableAt.hasDerivAt.tendsto_slope
  change Tendsto (fun δ => slope f 0 δ) _ _ at hfirst
  simp only [slope_def_field,hfzero,sub_zero] at hfirst
  have hfderiv : deriv f 0=0 := tendsto_nhds_unique hfirst hslope
  refine ⟨hfzero,hfderiv,?_⟩
  have hsecond := (quadratic_limit hf hfzero hfderiv).mul_const 2
  have hh : Tendsto (fun δ => f δ/δ^2) (𝓝[≠] 0) (𝓝 (deriv^[2] f 0/2)) := by
    convert hsecond using 1
    · ext δ
      ring
    · ring
  exact tendsto_nhds_unique hh ha

end polyak.FareyPlateau.FanAnalysis
