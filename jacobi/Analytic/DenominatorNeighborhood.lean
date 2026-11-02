import jacobi.Analytic.ResolventDomain
import Mathlib.Topology.MetricSpace.Thickening

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The common compact slit-domain denominator bound persists on a whole
neighbourhood of the original positive spectral interval. It therefore
controls actual finite spectra, not just the limiting Bessel spectrum.
Source: compactness, positive continuous denominators, and metric thickenings.
Use: the actual finite Jacobi spectra are L1-close to the genuine Bessel spectrum, so Lemma specw has no added finite nonvanishing premise.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Set Real Metric

/-- The original compact slit denominator bound persists uniformly
under a small real perturbation of every reciprocal spectral value.
Use: the actual finite Jacobi spectra are L1-close to the genuine
Bessel spectrum, so Lemma specw has no added finite nonvanishing premise.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the genuine inverse-denominator bound gives a positive lower
bound for its denominator on the compact spectral interval times W.
The open strict half-bound contains that compact set and hence a whole
positive metric thickening. Nearby genuine finite denominators retain
the same positive lower bound and a common inverse bound. -/
theorem denominator_neighborhood {s:ℝ} (hs:0<s) {W:Set ℂ} (hW:IsCompact W)
    (hsub:W⊆slitDomain s) :
    ∃δ C:ℝ,0<δ ∧ 0<C ∧ ∀w∈W,∀x y:ℝ,y∈Icc 0 (1/s) → |x-y|≤δ →
      1+(x:ℂ)*w≠0 ∧ ‖(1+(x:ℂ)*w)⁻¹‖≤C := by
  -- The compact set retains the zero spectral accumulation point.
  obtain ⟨B,hB,hbound⟩ := denominator_compact_bound hs hW hsub
  let K := W×ˢIcc (0:ℝ) (1/s)
  let U : Set (ℂ×ℝ) := {p | 1/(2*B)<‖1+(p.2:ℂ)*p.1‖}
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hKU : K⊆U := by
    rintro ⟨w,y⟩ ⟨hw,hy⟩
    have hne := slit_denominator_ne hs hy (hsub hw)
    have hn : ‖1+(y:ℂ)*w‖≠0 := norm_ne_zero_iff.mpr hne
    have hh := mul_le_mul_of_nonneg_right (hbound w hw y hy) (norm_nonneg (1+(y:ℂ)*w))
    rw [norm_inv,inv_mul_cancel₀ hn] at hh
    change 1/(2*B)<‖1+(y:ℂ)*w‖
    apply (div_lt_iff₀ (by positivity : 0<2*B)).mpr
    nlinarith
  obtain ⟨δ,hδ,hδU⟩ := (hW.prod isCompact_Icc).exists_cthickening_subset_open hU hKU
  refine ⟨δ,2*B,hδ,by positivity,fun w hw x y hy hxy => ?_⟩
  have hd : dist (w,x) (w,y)≤δ := by
    rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : (0:ℝ)≤dist x y)]
    exact hxy
  have hp := hδU (mem_cthickening_of_dist_le (w,x) (w,y) δ K ⟨hw,hy⟩ hd)
  change 1/(2*B)<‖1+(x:ℂ)*w‖ at hp
  have hpos : 0<‖1+(x:ℂ)*w‖ := (by positivity : (0:ℝ)<1/(2*B)).trans hp
  refine ⟨norm_ne_zero_iff.mp hpos.ne',?_⟩
  rw [norm_inv,inv_eq_one_div]
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_comm] using ((div_lt_iff₀ (by positivity : 0<2*B)).mp hp).le

end
end jacobi.EdgeResolvent
