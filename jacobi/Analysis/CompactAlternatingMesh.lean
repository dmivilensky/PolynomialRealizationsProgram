import jacobi.Analysis.AlternatingMesh
import jacobi.GelfandLevitan.ShrinkingIntegral
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
For every compact continuous family the entire normalized alternating
prefix sum vanishes uniformly over its parameters and prefix length.
Use: the actual two cross-edge K*F terms in the Cholesky residual and the opposite-edge K*f term in the eigenvector transform vanish uniformly.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- Every compact continuous family has uniformly vanishing normalized
alternating physical prefix sums, with all prefix parities included.
Use: the actual two cross-edge K*F terms in the Cholesky residual and
the opposite-edge K*f term in the eigenvector transform vanish uniformly.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: uniform continuity bounds every adjacent mesh oscillation.
The physical clamp is one-Lipschitz. The proved exact finite alternating
bound leaves at most half the mesh count times that oscillation and
one compact endpoint bound; division by the true mesh size removes both. -/
theorem compact_alternating_mesh_zero {P:Type*} [MetricSpace P] [CompactSpace P]
    (G:C(P×HalfInterval,ℝ)) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ m≤n, ∀ p:P,
      |(∑ j∈Finset.range m, (-1:ℝ)^j*
        G (p,halfParameterClamp ((j:ℝ)/(n:ℝ))))/(n:ℝ)|<ε := by
  -- Use one compact-family modulus for every parameter and every adjacent mesh pair.
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous G.continuous) ε hε
  have hone : Tendsto (fun n:ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hsmall : Tendsto (fun n:ℕ => ‖G‖/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((hone.eventually (Iio_mem_nhds hδ)).and
      ((hsmall.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<ε/2))).and (eventually_gt_atTop (0:ℕ))))
  refine ⟨N,fun n hn m hm p => ?_⟩
  obtain ⟨hstep,hend,hnpos⟩ := hN n hn
  have hnr : (0:ℝ)<(n:ℝ) := by exact_mod_cast hnpos
  let f (j:ℕ) := G (p,halfParameterClamp ((j:ℝ)/(n:ℝ)))
  have hbound (j:ℕ) : |f j|≤‖G‖ := by
    simpa only [Real.norm_eq_abs] using G.norm_coe_le_norm (p,halfParameterClamp ((j:ℝ)/(n:ℝ)))
  have hosc (j:ℕ) : |f j-f (j+1)|≤ε := by
    have hd : dist (p,halfParameterClamp ((j:ℝ)/(n:ℝ)))
        (p,halfParameterClamp (((j+1:ℕ):ℝ)/(n:ℝ)))<δ := by
      rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)]
      have hc := (LipschitzWith.projIcc (by norm_num : (0:ℝ)≤1/2)).dist_le_mul
        ((j:ℝ)/(n:ℝ)) (((j+1:ℕ):ℝ)/(n:ℝ))
      change dist (halfParameterClamp ((j:ℝ)/(n:ℝ)))
        (halfParameterClamp (((j+1:ℕ):ℝ)/(n:ℝ)))≤1*dist ((j:ℝ)/(n:ℝ)) (((j+1:ℕ):ℝ)/(n:ℝ)) at hc
      have he : dist ((j:ℝ)/(n:ℝ)) (((j+1:ℕ):ℝ)/(n:ℝ))=1/(n:ℝ) := by
        rw [Real.dist_eq]
        have hh : (j:ℝ)/(n:ℝ)-((j+1:ℕ):ℝ)/(n:ℝ)=-(1/(n:ℝ)) := by push_cast; ring
        rw [hh,abs_neg,abs_of_pos (by positivity)]
      rw [one_mul,he] at hc
      exact hc.trans_lt hstep
    exact (hclose hd).le
  have hh := alternating_sum_bound f (norm_nonneg G) m (fun j _ => hbound j) (fun j _ => hosc j)
  rw [abs_div,abs_of_pos hnr]
  apply (div_lt_iff₀ hnr).mpr
  have hc : 2*(m/2)≤n := by omega
  have hcr : 2*((m/2:ℕ):ℝ)≤(n:ℝ) := by exact_mod_cast hc
  have he : ‖G‖<(ε/2)*(n:ℝ) := (div_lt_iff₀ hnr).mp hend
  nlinarith

end
end jacobi.Analysis
