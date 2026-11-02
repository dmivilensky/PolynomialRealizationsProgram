import jacobi.Comparison.EmbeddedEigenvectors

/-!
Article: jacobi, Theorem 2.1.
The actual original step embeddings of every fixed signed target
eigenvector converge in the genuine physical L2 norm to the already
constructed full target basis. The proof uses the actual uniform row
limit and uniform continuity, without an assumed Hilbert-space limit.
Use: nuclear rank-one continuity and the actual L1 spectral limit prove trace-norm convergence of the embedded original inverse in Theorem 2.1.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual embedded original signed eigenvectors converge in L2
to the same genuine full target Hilbert basis used by H_alpha.
Use: nuclear rank-one continuity and the actual L1 spectral limit
prove trace-norm convergence of the embedded original inverse in Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: the genuine finite row error is uniformly small. Every actual
cell is within 1/N of its original left sample, so uniform continuity
of the same full wave bounds its actual cell oscillation. The resulting
almost-everywhere uniform error bounds the genuine L2 distance. -/
theorem embeddedTargetEigenvector_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => embeddedTargetEigenvector a b ha hb n k) atTop
      (𝓝 (fullTargetBasis a ha k:Space)) := by
  -- All representatives are those of the original embedding and the actual original basis vector.
  let M : ℝ := (measureUnivNNReal (volume:Measure Interval):ℝ)^((2:ℝ≥0∞).toReal⁻¹)
  have hM : 0≤M := Real.rpow_nonneg (by positivity) _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(4*(M+1))
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨N,hN⟩ := target_eigenvector_uniform_limit ha hb k η hη
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (fullWaveMap a ha k).continuous) η hη
  have hone : Tendsto (fun n:ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun n:ℕ => le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop N,hone.eventually (Iio_mem_nhds hδ)] with n hn hstep
  have hae : ∀ᵐ t:Interval ∂volume,
      ‖(embeddedTargetEigenvector a b ha hb n k-(fullTargetBasis a ha k:Space)) t‖≤2*η := by
    filter_upwards [Lp.coeFn_sub (embeddedTargetEigenvector a b ha hb n k) (fullTargetBasis a ha k:Space),
      embeddedTargetEigenvector_ae a b ha hb n k,fullTargetBasis_wave_ae a ha k,interval_interior_ae]
      with t hsub he hv ht
    let i := floorMatrixIndex n t.val ht
    have hc : t∈fullCell n i := floorMatrixIndex_mem_cell n t.val ht
    have hi := embeddedTargetEigenvector_cell a b ha hb n k i hc
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [he,hv,hi]
    rw [Real.norm_eq_abs]
    have hosc := hclose ((fullCell_matrix_distance n i hc).trans hstep)
    rw [Real.dist_eq] at hosc
    exact (abs_sub_le _ (fullWaveMap a ha k (matrixPoint n i)) _).trans
      (by linarith [hN n hn i])
  have hnorm : ‖embeddedTargetEigenvector a b ha hb n k-(fullTargetBasis a ha k:Space)‖≤M*(2*η) :=
    Lp.norm_le_of_ae_bound (by positivity) hae
  rw [dist_eq_norm]
  apply hnorm.trans_lt
  have hηeq : η*(4*(M+1))=ε := div_mul_cancel₀ _ (by positivity)
  nlinarith

end
end jacobi.Comparison
