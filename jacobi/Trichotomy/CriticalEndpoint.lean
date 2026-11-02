import jacobi.Analysis.AsymptoticSlope
import jacobi.GelfandLevitan.SineCase
import chebyshev2.SineContinuum.EndpointBounds

/-!
Article: jacobi, Proposition C.4.
The actual critical persymmetric profile is the previously verified
sine--Legendre profile. Its exact logarithmic leading coefficient follows
from the same no-logarithm branch and Wronskian two. No elliptic endpoint
expansion or unproved special-function asymptotic is required.
Use: critical_profile_limit combines this ratio with the independently proved no-logarithm normalization of the original left solution.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The true right-to-left sine selected-solution ratio has its exact leading logarithmic coefficient.
Use: critical_profile_limit combines this ratio with the independently proved no-logarithm normalization of the original left solution.
Article: jacobi, Proposition C.4.
Source: chebyshev2, Lemma 5, no-logarithm branch and exact Wronskian.
Proof: the actual ratio derivative is -2/l(t)^2 and l(t)^2/t tends
to pi. The logarithmic primitive theorem therefore gives ratio/log(t)
tending to -2/pi. -/
theorem critical_ratio_limit :
    Tendsto (fun t:ℝ=>chebyshev2.SineContinuum.ratio t/log t)
      (𝓝[>] (0:ℝ)) (𝓝 (-2/Real.pi)) := by
  -- The coefficient is fixed by the original genuine Wronskian, not an imposed asymptotic.
  have hd : ∀ᶠ t:ℝ in 𝓝[>] 0,
      HasDerivAt chebyshev2.SineContinuum.ratio
        (-2/(chebyshev2.SineContinuum.l t)^2) t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    exact chebyshev2.SineContinuum.ratio_derivative ht
  have h := (tendsto_const_nhds (x:=(-2:ℝ))).div
    chebyshev2.SineContinuum.l_square_boundary Real.pi_ne_zero
  have hl : Tendsto (fun t:ℝ=>t*(-2/(chebyshev2.SineContinuum.l t)^2))
      (𝓝[>] (0:ℝ)) (𝓝 (-2/Real.pi)) := by
    apply (tendsto_congr' ?_).mpr h
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t*(-2/(chebyshev2.SineContinuum.l t)^2)=
      -2/((chebyshev2.SineContinuum.l t)^2/t)
    field_simp
  exact jacobi.Analysis.logarithmic_endpoint_limit hd hl

/-- The actual critical persymmetric profile has exactly the printed asymptotic phi(t)~2*t*log(1/t).
Use: the critical support and double-exponential packing tail in Proposition C.4 start from this unconditional original-profile endpoint limit.
Article: jacobi, Proposition C.4.
Source: chebyshev2, the original sine--Legendre Green realization, reused without a new construction.
Proof: phi=l*r=(l^2/t)*(r/l)*t. Divide by t*log(1/t),
use log(1/t)=-log(t), and multiply the proved limits pi and -2/pi.
The source's actual profile is the same sine profile at every point. -/
theorem critical_profile_real_limit (ha:-1 < -(1/2:ℝ)) :
    Tendsto (fun t:ℝ=>persymmetricProfile (-(1/2)) ha
      ⟨max 0 (min 1 t),le_max_left _ _,by
        exact max_le (by norm_num) (min_le_left _ _)⟩/(t*log (1/t)))
      (𝓝[>] (0:ℝ)) (𝓝 2) := by
  -- The clamp is only a total real-coordinate representative; it is the identity on the genuine physical endpoint interval.
  have h := chebyshev2.SineContinuum.l_square_boundary.mul critical_ratio_limit
  have hv : Real.pi*(-2/Real.pi)=(-2:ℝ) := by field_simp
  rw [hv] at h
  have hn := h.neg
  simp only [neg_neg] at hn
  apply (tendsto_congr' ?_).mpr hn
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
  rw [sine_persymmetricProfile,chebyshev2.SineContinuum.phi_product]
  simp only [min_eq_right ht.2.le,max_eq_right ht.1.le,
    chebyshev2.SineContinuum.ratio,one_div,Real.log_inv]
  field_simp

/-- The critical original physical half-interval profile has exactly the printed logarithmic leading coefficient two.
Use: gives Proposition C.4's critical limit in the same physical coordinate and filter as the subcritical endpoint theorem, before constructing the packing tails.
Article: jacobi, Proposition C.4.
Proof: restrict the already proved real-coordinate critical limit to
the physical half interval. Its clamp is identically the original
coordinate there, so the unchanged genuine profile has the same limit. -/
theorem critical_profile_limit (ha:-1 < -(1/2:ℝ)) :
    Tendsto (fun t:HalfInterval=>persymmetricProfile (-(1/2)) ha (halfInclusion t)/
      ((t:ℝ)*log (1/(t:ℝ)))) (𝓝[>] halfZero) (𝓝 2) := by
  -- The original physical endpoint filter maps to the genuine right-hand real endpoint filter.
  have ht : Tendsto (fun t:HalfInterval=>(t:ℝ))
      (𝓝[>] halfZero) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      self_mem_nhdsWithin⟩
  have h := (critical_profile_real_limit ha).comp ht
  apply (tendsto_congr' ?_).mpr h
  apply Eventually.of_forall
  intro t
  have htle : (t:ℝ)≤1 := t.property.2.trans (by norm_num)
  simp only [Function.comp_def,min_eq_right htle,max_eq_right t.property.1]
  rfl

end
end jacobi.Trichotomy
