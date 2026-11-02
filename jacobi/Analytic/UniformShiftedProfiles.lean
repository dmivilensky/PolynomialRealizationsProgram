import jacobi.Analytic.FiniteShiftedProfiles
import jacobi.Analysis.ParameterMatrixCompactness
import jacobi.Comparison.EmbeddedEigenvectors

/-!
Article: jacobi, Theorem C.5.
The original actual finite shifted diagonal spectral sums converge
uniformly over the full physical matrix range and each compact shift
set. Their eventual common bound and exact floor-row limits follow
with all finite spectral and eigenvector premises discharged.
Use: Theorem C.5's actual matrix identity transfers this full estimate to the source resolvents and their normalized shifted energies.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Comparison
open scoped Topology

/-- The original finite shifted diagonal spectral sums converge to the
same genuine shifted profile uniformly over all physical rows and
all parameters in each original compact slit-domain set.
Use: Theorem C.5's actual matrix identity transfers this full estimate
to the source resolvents and their normalized shifted energies.
Article: jacobi, Theorem C.5.
Proof: the true moving-row/parameter limit is already proved from the
original eigenvectors and spectra. Joint continuity of the actual
continuum profile gives the same moving sample limit. Compactness of
the original physical interval times W makes the actual error uniform. -/
theorem finiteShiftedDiagonal_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i:Fin (n+1),∀w∈W,
      ‖finiteShiftedDiagonal a b ha hb n i w-shiftedProfile a ha (matrixPoint n i) w‖<ε := by
  -- Compactness retains both original physical endpoints and the whole genuine shift set.
  let _ : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let err (n:ℕ) (i:Fin (n+1)) (w:W) :=
    finiteShiftedDiagonal a b ha hb n i w-shiftedProfile a ha (matrixPoint n i) w
  have hu := parameter_matrix_uniform_zero err (by
    intro ns hns i t hit w w0 hw
    have hp : Tendsto (fun r => matrixPoint (ns r) (i r)) atTop (𝓝 t) := tendsto_subtype_rng.mpr hit
    have hprofile := (shiftedProfile_joint_continuous a ha hW hsub).continuousAt.tendsto.comp (hp.prodMk_nhds hw)
    have hfinite := finiteShiftedDiagonal_moving_limit ha hb hW hsub ns hns i hit w hw
    simpa only [err,Function.comp_def,sub_self] using hfinite.sub hprofile)
  intro ε hε
  obtain ⟨N,hN⟩ := hu ε hε
  exact ⟨N,fun n hn i w hw => hN n hn i ⟨w,hw⟩⟩

/-- The genuine finite shifted diagonal spectral sums have one common
eventual bound over all original physical rows and compact shifts.
Use: the original complex-resolvent identity yields precisely Theorem C.5,
and the same genuine bound controls both energy limits in Theorem C.5.
Article: jacobi, Theorem C.5.
Proof: the actual uniform profile error is eventually below one; the
same actual continuum profile has a proved common compact bound. -/
theorem finiteShiftedDiagonal_bound {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i:Fin (n+1),∀w∈W,
      ‖finiteShiftedDiagonal a b ha hb n i w‖≤C := by
  obtain ⟨B,hB,hbound⟩ := shiftedProfile_compact_bound a ha hW hsub
  obtain ⟨N,hN⟩ := finiteShiftedDiagonal_uniform ha hb hW hsub 1 (by norm_num)
  refine ⟨B+1,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn i w hw
  have hh := norm_add_le (finiteShiftedDiagonal a b ha hb n i w-shiftedProfile a ha (matrixPoint n i) w)
    (shiftedProfile a ha (matrixPoint n i) w)
  rw [sub_add_cancel] at hh
  linarith [hN n hn i w hw,hbound (matrixPoint n i) w hw]

/-- At the exact source floor row the actual finite shifted diagonal
spectral sums converge uniformly on the full original compact shift set.
Use: after the actual complex-matrix identification this is exactly
Theorem C.5, with the same physical and edge-shift conventions.
Article: jacobi, Theorem C.5.
Proof: the actual full-row approximation is already uniform. The
original floor cell is within 1/N of its physical point. Uniform
continuity of the same genuine profile on [0,1] times W eliminates
that cell discrepancy uniformly in the original shift parameter. -/
theorem finiteShiftedDiagonal_floor_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha)
    (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀w∈W,
      ‖finiteShiftedDiagonal a b ha hb n (floorMatrixIndex n t ht) w-
        shiftedProfile a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ w‖<ε := by
  -- One joint compact modulus applies to every original shift simultaneously.
  let _ : CompactSpace W := isCompact_iff_compactSpace.mp hW
  intro ε hε
  obtain ⟨N,hN⟩ := finiteShiftedDiagonal_uniform ha hb hW hsub (ε/2) (by positivity)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (shiftedProfile_joint_continuous a ha hW hsub)) (ε/2) (by positivity)
  have hone : Tendsto (fun n:ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun n:ℕ => le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) tendsto_natCast_atTop_atTop)
  obtain ⟨NC,hNC⟩ := eventually_atTop.mp (hone.eventually (Iio_mem_nhds hδ))
  refine ⟨max N NC,fun n hn w hw => ?_⟩
  have hd : dist (matrixPoint n (floorMatrixIndex n t ht),(⟨w,hw⟩:W))
      ((⟨t,⟨ht.1.le,ht.2.le⟩⟩:Interval),(⟨w,hw⟩:W))<δ := by
    rw [Prod.dist_eq,dist_self,max_eq_left dist_nonneg]
    exact (fullCell_matrix_distance n _ (floorMatrixIndex_mem_cell n t ht)).trans (hNC n (by omega))
  have hh := norm_sub_le_norm_sub_add_norm_sub (finiteShiftedDiagonal a b ha hb n (floorMatrixIndex n t ht) w)
    (shiftedProfile a ha (matrixPoint n (floorMatrixIndex n t ht)) w)
    (shiftedProfile a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ w)
  have hc := hclose hd
  rw [dist_eq_norm] at hc
  exact hh.trans_lt (by linarith [hN n (by omega) (floorMatrixIndex n t ht) w hw])

end
end jacobi.EdgeResolvent
