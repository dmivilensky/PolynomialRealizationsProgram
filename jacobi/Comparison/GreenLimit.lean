import jacobi.Comparison.GreenSpectral
import jacobi.Analysis.WeightedSeriesLimit
import jacobi.GelfandLevitan.TargetGreenKernel

/-!
Article: jacobi, Theorem 2.1.
Every actual target Green entry has the printed continuum limit along
arbitrary cofinal moving rows on the whole closed physical interval.
The diagonal is the original persymmetric profile, and exact floor
rows give the Green-matrix assertion of Theorem 2.1.
Use: its diagonal proves the profile part of Theorem 2.1; exact floor rows prove the full matrix-entry assertion of Theorem 2.1.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology

/-- Every actual normalized target Green entry converges to twice the
original full Green kernel along arbitrary cofinal physical row pairs.
Use: its diagonal proves the profile part of Theorem 2.1; exact floor
rows prove the full matrix-entry assertion of Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: sum the genuine signed vector-product limits against the true
Jacobi spectrum. The proved full uniform eigenvector bound controls
every spectral observable and the actual L1 limit controls all tails.
The remaining original Bessel-wave series is precisely twice the
already constructed genuine Green kernel of the full operator. -/
theorem scaledTargetGreen_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i j:∀r:ℕ,Fin (ns r+1))
    {t s:Interval}
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/((ns r:ℝ)+1)) atTop (𝓝 (t:ℝ)))
    (hjs:Tendsto (fun r:ℕ => ((j r).val:ℝ)/((ns r:ℝ)+1)) atTop (𝓝 (s:ℝ))) :
    Tendsto (fun r => scaledTargetGreen a b ha hb (ns r) (i r) (j r)) atTop
      (𝓝 (2*targetGreenKernel a ha t s)) := by
  -- The same complete finite spectrum is used in both the original Green matrix and its L1 limit.
  obtain ⟨C,_,hC⟩ := scaledTargetEigenvector_bound ha hb
  have hdim : Tendsto (fun r => ns r+1) atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_succ _) hns
  have hh := weighted_series_limit
    (r:=fun r k => jacobi.Jacobi.finiteLambdaAt a b ha hb (ns r+1) k)
    (L:= jacobi.Bessel.edgeValue a ha)
    (f:=fun r k => scaledTargetEigenvector a b ha hb (ns r) (i r) k*
      scaledTargetEigenvector a b ha hb (ns r) (j r) k)
    (g:=fun k => fullWaveMap a ha k t*fullWaveMap a ha k s)
    (fun r => jacobi.Jacobi.finiteLambdaAt_summable ha hb (ns r+1))
    (jacobi.Bessel.edgeValue_summable ha) ((jacobi.Jacobi.finiteLambdaAt_l1_tendsto ha hb).comp hdim)
    (C:=C*C) (by
      filter_upwards [hns.eventually hC] with r hr k
      rw [abs_mul]
      exact mul_le_mul (hr (i r) k) (hr (j r) k) (abs_nonneg _) (le_trans (abs_nonneg _) (hr (i r) k)))
    (fun k => (target_eigenvector_full_limit ha hb k ns hns i hit).mul
      (target_eigenvector_full_limit ha hb k ns hns j hjs))
  have he : (∑'k,jacobi.Bessel.edgeValue a ha k*(fullWaveMap a ha k t*fullWaveMap a ha k s))=
      2*targetGreenKernel a ha t s := by
    rw [targetGreenKernel_apply,← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [jacobi.Bessel.edgeValue]
    ring
  rw [he] at hh
  simpa only [scaledTargetGreen_spectral] using hh

/-- The genuine actual finite resolvent diagonal has the full original
persymmetric-profile limit along every cofinal moving physical row.
Use: floor specialization is Theorem 2.1's diagonal conclusion, and the
common actual bound gives its energy limit by dominated convergence.
Article: jacobi, Proposition 2.2.
Proof: the actual full Green-matrix limit applies on the diagonal;
the independently proved genuine Green diagonal is phi_alpha/2. -/
theorem scaledTargetDiagonal_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    {t:Interval} (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/((ns r:ℝ)+1)) atTop (𝓝 (t:ℝ))) :
    Tendsto (fun r => scaledTargetGreen a b ha hb (ns r) (i r) (i r)) atTop
      (𝓝 (persymmetricProfile a ha t)) := by
  have hh := scaledTargetGreen_limit ha hb ns hns i i hit hit
  simpa only [targetGreen_diagonal,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hh

/-- At the exact two physical floor rows the actual finite target
Green matrix has precisely the printed original full-kernel limit.
Use: this proves the matrix-entry assertion of Theorem 2.1 for the
same canonical candidate, with no additional eigenvector assumptions.
Article: jacobi, Theorem 2.1.
Proof: specialize the proved full moving-row Green limit using the
genuine finite floor indices and their actual matrix-size mesh limits. -/
theorem scaledTargetGreen_floor_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (t s:ℝ) (ht:t∈Ioo (0:ℝ) 1) (hs:s∈Ioo (0:ℝ) 1) :
    Tendsto (fun n:ℕ => scaledTargetGreen a b ha hb n
      (floorMatrixIndex n t ht) (floorMatrixIndex n s hs)) atTop
      (𝓝 (2*targetGreenKernel a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ ⟨s,⟨hs.1.le,hs.2.le⟩⟩)) :=
  scaledTargetGreen_limit ha hb id tendsto_id (fun n => floorMatrixIndex n t ht)
    (fun n => floorMatrixIndex n s hs) (floorMatrixMesh_tendsto t ht) (floorMatrixMesh_tendsto s hs)

end
end jacobi.Comparison
