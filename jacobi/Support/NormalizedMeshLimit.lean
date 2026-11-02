import jacobi.Support.NormalizedMesh

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The actual ground-normalized finite Volterra operator converges along
every moving physical half-chain endpoint. Its original two-index
kernel, both triangular cutoffs and the singular corner are all
handled before applying bounded double-mesh dominated convergence.
Use: groundMeshData_limit proves that the original finite triangular and terminal cutoffs converge away from their measure-zero limiting boundaries.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter Finset MeasureTheory jacobi.Reference
open scoped Topology

/-- Strict separation of two limiting mesh ratios eventually separates their original integer indices.
Use: groundMeshData_limit proves that the original finite triangular and terminal cutoffs converge away from their measure-zero limiting boundaries.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: strict order is stable under convergence of real numbers.
Proof: the two ratios are eventually strictly ordered; multiplication by the same positive cofinal degree preserves their order, and natural casts reflect it. -/
theorem mesh_index_eventually_lt {ι:Type*} {l:Filter ι} {n j k:ι→ℕ} {s t:ℝ}
    (hn:Tendsto n l atTop) (hj:Tendsto (fun i => (j i:ℝ)/(n i:ℝ)) l (𝓝 s))
    (hk:Tendsto (fun i => (k i:ℝ)/(n i:ℝ)) l (𝓝 t)) (hst:s<t) :
    ∀ᶠi in l,j i<k i := by
  filter_upwards [hn.eventually_gt_atTop 0,hj.eventually_lt hk hst] with i hi hij
  have hnR : (0:ℝ)<n i := by exact_mod_cast hi
  exact_mod_cast (div_lt_div_iff_of_pos_right hnR).mp hij

/-- The genuine finite zero-extended double mesh converges at every interior rectangle point away from its actual moving cutoff boundaries.
Use: finiteGroundMesh_limit applies bounded double-mesh convergence to the original support operator, with only two measure-zero lines excluded.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: floor mesh ratios converge to their original spatial coordinates. Strict separation makes the actual finite cutoffs eventually constant. In the surviving triangle, the proved actual normalized kernel limit and continuity of the genuine regular factor give the original continuum integrand. -/
theorem groundMeshData_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {ι:Type*} {l:Filter ι} {n m:ι→ℕ} {t r s:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t))
    {q:ℝ→ℂ} (hq:ContinuousOn q (Icc (0:ℝ) (1/2)))
    (hr:r∈Ioo (0:ℝ) 1) (hs:s∈Ioo (0:ℝ) 1) (hrt:r≠t) (hsr:s≠r) :
    Tendsto (fun i => groundMeshData a b ha hb (n i) (m i) q
      (Nat.floor ((n i:ℝ)*r)) (Nat.floor ((n i:ℝ)*s))) l (𝓝 (groundRectangle a q t r s)) := by
  -- The original finite integration domain is not replaced by a presumed limiting triangle.
  let jr (i:ι) := Nat.floor ((n i:ℝ)*r)
  let js (i:ι) := Nat.floor ((n i:ℝ)*s)
  have hjr : Tendsto (fun i => (jr i:ℝ)/(n i:ℝ)) l (𝓝 r) :=
    chebyshev1.Analysis.floor_mesh_limit hn tendsto_const_nhds (Eventually.of_forall (fun _ => hr.1.le))
  have hjs : Tendsto (fun i => (js i:ℝ)/(n i:ℝ)) l (𝓝 s) :=
    chebyshev1.Analysis.floor_mesh_limit hn tendsto_const_nhds (Eventually.of_forall (fun _ => hs.1.le))
  rcases lt_or_gt_of_ne hrt with hrt | htr
  · rcases lt_or_gt_of_ne hsr with hsr | hrs
    · have hri : r∈Ioo (0:ℝ) (1/2) := ⟨hr.1,hrt.trans_le ht.2⟩
      have hsi : s∈Ioo (0:ℝ) r := ⟨hs.1,hsr⟩
      have hK := normalizedKernel_limit ha hb hri hsi hn hjr hjs
      have hKc : Tendsto (fun i => (normalizedKernel a b ha hb (n i) (jr i) (js i):ℂ)) l
          (𝓝 (2*(weight a s:ℂ)^2/(weight a r:ℂ)^2)) := by
        simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
          Complex.ofReal_ofNat] using Complex.continuous_ofReal.continuousAt.tendsto.comp hK
      have hqc := hq.continuousAt (Icc_mem_nhds hs.1 (by linarith [hsr,hri.2]))
      have hlim := hKc.mul (hqc.tendsto.comp hjs)
      simp only [groundRectangle,ite_eq_left hrt.le,ite_eq_left hsr.le]
      apply (tendsto_congr' ?_).mpr hlim
      filter_upwards [mesh_index_eventually_lt hn hjr hm hrt,
        mesh_index_eventually_lt hn hjs hjr hsr] with i hi hij
      simp only [groundMeshData,ite_eq_left (show jr i<m i ∧ js i≤jr i from ⟨hi,hij.le⟩),
        jr,js,Function.comp_def]
    · have hz : groundRectangle a q t r s=0 := by simp [groundRectangle,hrt.le,not_le.mpr hrs]
      rw [hz]
      apply tendsto_const_nhds.congr'
      filter_upwards [mesh_index_eventually_lt hn hjr hjs hrs] with i hij
      simp only [groundMeshData,ite_eq_right (show ¬(jr i<m i ∧ js i≤jr i) by omega),jr,js]
  · have hz : groundRectangle a q t r s=0 := by simp [groundRectangle,not_le.mpr htr]
    rw [hz]
    apply tendsto_const_nhds.congr'
    filter_upwards [mesh_index_eventually_lt hn hm hjr htr] with i hi
    simp only [groundMeshData,ite_eq_right (show ¬(jr i<m i ∧ js i≤jr i) by omega),jr,js]

/-- The actual normalized finite Volterra operator converges to twice the genuine continuum operator along every moving physical half-chain endpoint, including zero.
Use: the complex support edge proof obtains a uniformly vanishing residual for the actual reference core in the original finite equations; finite Gronwall then controls the actual complex polynomials.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the true finite kernel has a uniform bound before integration. Compact continuity bounds the same actual regular factor at every used mesh point. The original zero-extended integrands converge away from the two null cutoff lines, so bounded double-mesh convergence applies on a fixed rectangle. Its integral equals twice the already defined genuine nested continuum operator. -/
theorem finiteGroundMesh_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {ι:Type*} {l:Filter ι} [l.IsCountablyGenerated] {n m:ι→ℕ} {t:ℝ}
    (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t))
    (hhalf:∀ᶠi in l,2*m i≤n i+1) (ht:t∈Icc (0:ℝ) (1/2))
    {q:ℝ→ℂ} (hq:ContinuousOn q (Icc (0:ℝ) (1/2))) :
    Tendsto (fun i => finiteGroundMesh a b ha hb (n i) (m i) q) l
      (𝓝 (2*groundVolterra a q t)) := by
  -- A single constant dominates the actual kernel even at its zero corner.
  obtain ⟨B,hB,hbound⟩ := normalizedKernel_bound ha hb
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s:=Icc (0:ℝ) (1/2)) hq
  have hbnd : ∀ᶠi in l,∀j k,‖groundMeshData a b ha hb (n i) (m i) q j k‖≤B*max C 0 := by
    filter_upwards [hn.eventually hbound,hhalf,hn.eventually_gt_atTop 0] with i hi hmhalf hni
    intro j k
    by_cases hjk:j<m i ∧ k≤j
    · rw [groundMeshData,ite_eq_left hjk,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (hi j k (by omega) hjk.2).1]
      have hniR : (0:ℝ)<n i := by exact_mod_cast hni
      have hki : (k:ℝ)/(n i:ℝ)∈Icc (0:ℝ) (1/2) := by
        refine ⟨by positivity,?_⟩
        apply (div_le_iff₀ hniR).mpr
        have : 2*(k:ℝ)≤n i := by exact_mod_cast (show 2*k≤n i by omega)
        linarith
      exact mul_le_mul (hi j k (by omega) hjk.2).2 ((hC _ hki).trans (le_max_left _ _))
        (norm_nonneg _) hB.le
    · rw [groundMeshData,ite_eq_right hjk,norm_zero]
      positivity
  have hp : ∀ᵐr ∂volume.restrict (Ioo (0:ℝ) 1),∀ᵐs ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun i => groundMeshData a b ha hb (n i) (m i) q
        (Nat.floor ((n i:ℝ)*r)) (Nat.floor ((n i:ℝ)*s))) l (𝓝 (groundRectangle a q t r s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae (volume.ae_ne t)] with r hr hrt
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae (volume.ae_ne r)] with s hs hsr
    exact groundMeshData_limit ha hb ht hn hm hq hr hs hrt hsr
  have hlim := jacobi.Analysis.bounded_double_mesh_limit n
    (fun i => groundMeshData a b ha hb (n i) (m i) q) (groundRectangle a q t) hn hbnd hp
  rw [groundRectangle_integral a q ht] at hlim
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [hhalf,hn.eventually_gt_atTop 0] with i hi hni
  exact (finiteGroundMesh_integral a b ha hb hni (by omega) q).symm.trans
    (jacobi.Analysis.double_mesh_integral (n i) _ hni)

end
end jacobi.Support
