import jacobi.GelfandLevitan.SelectedEndpoint
import jacobi.GelfandLevitan.Profiles
import jacobi.Reference.BesselFrequency

/-!
Article: jacobi, Proposition C.4.
The original selected branch gives u_k(t)/t^gamma -> 1 for every
spectral index. The genuine strip estimate gives one bound for these
ratios over the entire original spectrum and physical half interval.
These are the inputs for summing the endpoint limit in the regime gamma<1/2.
Use: the genuine endpoint profile series factors into its spectral weights times normalizedEndpointWave squared.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The actual original transformed spectral wave divided by its selected endpoint power.
Use: the genuine endpoint profile series factors into its spectral weights times normalizedEndpointWave squared.
Article: jacobi, Proposition C.4.
-/
def normalizedEndpointWave (a:ℝ) (ha:-1<a) (k:ℕ) (t:HalfInterval) : ℝ :=
  realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t/(t:ℝ)^(gamma a)

/-- Every original normalized endpoint wave has the exact selected-branch limit one.
Use: the subcritical endpoint coefficient is the sum of the genuine original spectral weights, with no unproved modewise limit premise.
Article: jacobi, Proposition C.4.
Proof: the proved actual selected-branch error is bounded by C*t on
the original right endpoint filter. Squeeze its complex norm to zero,
then take the real part, which is the same original real wave ratio. -/
theorem normalizedEndpointWave_limit (a:ℝ) (ha:-1<a) (k:ℕ) :
    Tendsto (normalizedEndpointWave a ha k) (𝓝[>] halfZero) (𝓝 1) := by
  -- The endpoint filter is the actual half interval, rather than an independently specified positive sequence.
  obtain ⟨C,hC,hbound⟩ := transformedSolution_selected_branch a ha (jacobi.Bessel.sigma a ha k:ℂ)
  have ht : Tendsto (fun t:HalfInterval => (t:ℝ)) (𝓝[>] halfZero) (𝓝 0) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t:HalfInterval => transformedSolution a ha t (jacobi.Bessel.sigma a ha k:ℂ)/
      (((t:ℝ)^(gamma a):ℝ):ℂ)-1) (𝓝[>] halfZero) (𝓝 0) :=
    squeeze_zero_norm' hbound (by simpa only [mul_zero] using ht.const_mul C)
  have h := Complex.continuous_re.continuousAt.tendsto.comp (hz.add_const 1)
  change Tendsto (fun t:HalfInterval =>
    (transformedSolution a ha t (jacobi.Bessel.sigma a ha k:ℂ)).re/(t:ℝ)^(gamma a))
      (𝓝[>] halfZero) (𝓝 1)
  simpa only [sub_add_cancel,Complex.zero_re,zero_add,Complex.one_re,
    Complex.div_ofReal_re,
    Function.comp_def] using h

/-- One genuine positive constant bounds every normalized transformed endpoint wave at every original spectral index.
Use: dominated convergence of the actual endpoint profile series requires a common all-mode bound, including the finite low-frequency prefix.
Article: jacobi, Proposition C.4.
Proof: insert the actual positive real Bessel frequencies into the
proved original strip estimate. Its minimum is at most t^gamma.
Divide by the same positive power at t>0; the totalized zero endpoint
ratio is exactly zero because gamma>0. -/
theorem normalizedEndpointWave_bound (a:ℝ) (ha:-1<a) :
    ∃C:ℝ,0<C ∧ ∀k:ℕ,∀t:HalfInterval,|normalizedEndpointWave a ha k t|≤C := by
  -- The frequency is the actual square root of sigma_k-c_0, whose positive gap was already proved.
  obtain ⟨C,hC,hbound⟩ := transformedSolution_strip_bound a ha 0
  refine ⟨C,hC,fun k t => ?_⟩
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  by_cases ht:0<(t:ℝ)
  · have he : (jacobi.Jacobi.endpointCorrection a:ℂ)+(besselFrequency a ha k:ℂ)^2=
        (jacobi.Bessel.sigma a ha k:ℂ) := by
      rw [← Complex.ofReal_pow,besselFrequency_sq]
      push_cast
      ring
    have hb := hbound (besselFrequency a ha k:ℂ)
      (Complex.ofReal_ne_zero.mpr (besselFrequency_pos ha k).ne') (by simp) t
    rw [he] at hb
    have hp := Real.rpow_pos_of_pos ht (gamma a)
    have hu : |realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t|≤C*(t:ℝ)^(gamma a) :=
      (Complex.abs_re_le_norm _).trans (hb.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le))
    rw [normalizedEndpointWave,abs_div,abs_of_pos hp,div_le_iff₀ hp]
    exact hu
  · have ht0 : (t:ℝ)=0 := le_antisymm (not_lt.mp ht) t.property.1
    simp only [normalizedEndpointWave,ht0,Real.zero_rpow hg.ne',div_zero,abs_zero]
    exact hC.le

end
end jacobi.Trichotomy
