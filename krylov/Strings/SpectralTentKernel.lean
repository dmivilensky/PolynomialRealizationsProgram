import krylov.Strings.SpectralEnergy
import krylov.Strings.SpectralTents

/-!
Article: `main_krylov`, `thm:value`, no boundary spectral mass at zero for
the bounded energy resolvent. Actual shrinking tent pairs belong to the
closed physical energy graph, and their mass coordinates converge to the
true boundary vector. Every compression-kernel vector is therefore
orthogonal to that boundary vector; no density assumption is introduced.
-/
namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable (M : Mass) [IsFiniteMeasure M.measure]

theorem boundaryTent_mem_energyGraph (n : ℕ) :
    WithLp.toLp 2 (boundaryTent M n, boundaryTentGradient n) ∈ energyGraph M :=
  energyGraph_mem_of_ae M _ _ (boundaryTent_energy_ae M n)

/-- No kernel vector of the actual Neumann resolvent sees the distinguished
boundary atom. -/
theorem neumann_kernel_boundary_inner {v : MassHilbert M}
    (hv : neumannResolvent M v = 0) : inner ℂ (boundaryVector M) v = 0 := by
  have horth := (compressedProjection_eq_zero_iff (energyGraph M).toSubmodule v).mp hv
  have ht (n : ℕ) : inner ℂ (boundaryTent M n) v = 0 := by
    have hh := ((energyGraph M).toSubmodule.mem_orthogonal _).mp horth _ (boundaryTent_mem_energyGraph M n)
    simpa only [firstInclusion_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
      WithLp.ofLp_fst, WithLp.ofLp_snd, inner_zero_right, add_zero] using hh
  have hlim : Tendsto (fun n ↦ inner ℂ (boundaryTent M n) v) atTop
      (𝓝 (inner ℂ (boundaryVector M) v)) :=
    (boundaryTent_tendsto M).inner (tendsto_const_nhds (x := v))
  have hzero : Tendsto (fun n ↦ inner ℂ (boundaryTent M n) v) atTop (𝓝 (0 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n ↦ (ht n).symm
  exact tendsto_nhds_unique hlim hzero

/-- The actual boundary vector has zero orthogonal projection onto the
Neumann resolvent kernel. -/
theorem boundary_orthogonal_neumann_kernel :
    boundaryVector M ∈ (neumannResolvent M).kerᗮ := by
  apply ((neumannResolvent M).ker.mem_orthogonal _).mpr
  intro v hv
  have hh := neumann_kernel_boundary_inner M (show neumannResolvent M v = 0 from hv)
  rw [← inner_conj_symm, hh, map_zero]

theorem boundary_neumann_kernel_projection_zero :
    (neumannResolvent M).ker.starProjection (boundaryVector M) = 0 := by
  have hh := boundary_orthogonal_neumann_kernel M
  rw [← (neumannResolvent M).ker.ker_starProjection] at hh
  exact hh

end
end krylov.Strings.Spectral
