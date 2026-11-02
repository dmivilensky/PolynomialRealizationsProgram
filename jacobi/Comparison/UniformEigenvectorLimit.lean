import jacobi.Comparison.EigenvectorLimit
import jacobi.GelfandLevitan.FullWaveReflection
import jacobi.Analysis.MatrixReflection

/-!
Article: jacobi, Proposition C.3.
The actual fixed spectral eigenvector converges uniformly, on the full
physical chain, to the same continuous signed wave of Proposition C.2. This
also proves every moving-row limit without a parity or midpoint exception.
Use: target_eigenvector_uniform_limit extends this actual estimate by physical reversal to every original row, with its unchanged sign.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology

/-- The genuine signed eigenvector limit is uniform on the entire
original physical half chain, including zero and the middle row.
Use: target_eigenvector_uniform_limit extends this actual estimate by
physical reversal to every original row, with its unchanged sign.
Article: jacobi, Proposition C.3.
Proof: the genuine moving-index limit and continuity of the actual
full wave make every cofinal moving half-row error vanish. Compactness
of the original closed physical half interval gives uniform vanishing. -/
theorem target_eigenvector_half_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀n≥N,∀i:Fin (n+1),2*i.val≤n+1 →
      |sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i k-
        fullWaveMap a ha k (matrixPoint n i)|<ε := by
  -- The compactness argument uses the same original signed entries, not their squares.
  let err (n:ℕ) (i _:Fin (n+1)) := sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i k-
    fullWaveMap a ha k (matrixPoint n i)
  have hu := half_matrix_uniform_zero err (by
    intro ns hns i _ hi _ t ht _ _ hit _
    have hsize := degree_to_size_mesh (m:=fun r => (i r).val) hns hit
    have hp : Tendsto (fun r => matrixPoint (ns r) (i r)) atTop
        (𝓝 (halfInclusion (⟨t,ht⟩:HalfInterval))) := tendsto_subtype_rng.mpr hsize
    have hfinite := target_eigenvector_half_limit ha hb k ns hns i (Eventually.of_forall hi) ht hsize
    have hwave := (fullWaveMap a ha k).continuous.continuousAt.tendsto.comp hp
    have hh := hfinite.sub hwave
    have he : fullWaveMap a ha k (halfInclusion ⟨t,ht⟩)=
        targetWaveScale a ha k*realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) ⟨t,ht⟩ := by
      rw [fullWaveMap_half a ha k _ ht.2]
      rfl
    rw [he,sub_self] at hh
    exact hh)
  intro ε hε
  obtain ⟨N,hN⟩ := hu ε hε
  refine ⟨N,fun n hn i hi => ?_⟩
  simpa only [Real.norm_eq_abs] using hN n hn i 0 hi (by simp)

/-- Every fixed actual spectral eigenvector has its full uniform signed
continuum limit on the original entire physical matrix chain.
Use: the moving-row and floor-row limits give Theorem 2.1; their
uniform error also controls the embedded L2 eigenvectors in Theorem 2.1.
Article: jacobi, Proposition C.3.
Proof: the true half-chain convergence is already uniform. Reversal
preserves the actual spectral sign. Its physical left endpoint differs
from continuum reflection by precisely one cell, whose effect vanishes
by uniform continuity of the same genuine full wave. -/
theorem target_eigenvector_uniform_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀n≥N,∀i:Fin (n+1),
      |sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i k-
        fullWaveMap a ha k (matrixPoint n i)|<ε := by
  -- A common modulus controls the genuine full wave across the midpoint as well.
  intro ε hε
  obtain ⟨NH,hNH⟩ := target_eigenvector_half_uniform ha hb k (ε/2) (by positivity)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (fullWaveMap a ha k).continuous) (ε/2) (by positivity)
  have hone : Tendsto (fun n:ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun n:ℕ => le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) tendsto_natCast_atTop_atTop)
  obtain ⟨NC,hNC⟩ := eventually_atTop.mp (hone.eventually (Iio_mem_nhds hδ))
  refine ⟨max NH NC,fun n hn i => ?_⟩
  by_cases hi:2*i.val≤n+1
  · exact (hNH n (by omega) i hi).trans (by linarith)
  · have hr : 2*i.rev.val≤n+1 := by simp only [Fin.val_rev]; omega
    have he := hNH n (by omega) i.rev hr
    have hd := hclose (show dist (matrixPoint n i.rev)
      (physicalReflection (matrixPoint n i))<δ by
        rw [matrixPoint_reflection_distance]; exact hNC n (by omega))
    have hs : (-1:ℝ)^k*((-1:ℝ)^k)=1 := by rw [← pow_two,← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    have hp := targetEigenvectorEntry_parity a b ha hb n i.rev k
    rw [Fin.rev_rev] at hp
    have hE : sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i k-
        fullWaveMap a ha k (matrixPoint n i)=
      (-1:ℝ)^k*(sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i.rev k-
        fullWaveMap a ha k (physicalReflection (matrixPoint n i))) := by
      rw [hp,fullWaveMap_reflection]
      nlinarith [congrArg (fun x:ℝ => x*fullWaveMap a ha k (matrixPoint n i)) hs]
    rw [hE,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    exact (abs_sub_le _ (fullWaveMap a ha k (matrixPoint n i.rev)) _).trans_lt
      (by have hh := add_lt_add he hd; rw [Real.dist_eq] at hh; linarith)

/-- The actual normalized signed eigenvector converges to the genuine
full target wave along every cofinal moving physical row.
Use: floor-row specialization gives Theorem 2.1, and arbitrary pairs
of such rows give the full Green-matrix limit in Theorem 2.1.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: the proved uniform actual row error vanishes; continuity of the
same full wave supplies its moving-coordinate limit on the closed interval. -/
theorem target_eigenvector_full_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    {t:Interval} (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/((ns r:ℝ)+1)) atTop (𝓝 (t:ℝ))) :
    Tendsto (fun r => sqrt ((ns r:ℝ)+1)*targetEigenvectorEntry a b ha hb (ns r) (i r) k)
      atTop (𝓝 (fullWaveMap a ha k t)) := by
  -- Uniform convergence allows every original moving row, including parity changes at the middle.
  have herr : Tendsto (fun r => sqrt ((ns r:ℝ)+1)*targetEigenvectorEntry a b ha hb (ns r) (i r) k-
      fullWaveMap a ha k (matrixPoint (ns r) (i r))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := target_eigenvector_uniform_limit ha hb k ε hε
    filter_upwards [hns.eventually_ge_atTop N] with r hr
    simpa only [Real.dist_eq,sub_zero] using hN (ns r) hr (i r)
  have hp : Tendsto (fun r => matrixPoint (ns r) (i r)) atTop (𝓝 t) := tendsto_subtype_rng.mpr hit
  have hh := herr.add ((fullWaveMap a ha k).continuous.continuousAt.tendsto.comp hp)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hh

end
end jacobi.Comparison
