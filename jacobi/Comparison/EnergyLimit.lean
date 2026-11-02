import jacobi.Comparison.UniformGreenLimit
import jacobi.Analysis.SuccessorMeshIntegral

/-!
Article: jacobi, Theorem 2.1.
The genuine full persymmetric Green-diagonal limit gives the exact
original N-cubed energy limit, with the same actual c_star integral
constructed by Proposition C.2. Every dependence on beta disappears.
Use: the upper bound in Theorems A--B compares the entire finite fibre infimum with this same actual persymmetric candidate.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The genuine canonical candidate has exactly the original printed
energy limit, with no remaining eigenvector or numerical premise.
Use: the upper bound in Theorems A--B compares the entire finite fibre
infimum with this same actual persymmetric candidate.
Article: jacobi, Theorem 2.1.
Proof: extend the same original continuous profile by physical clipping.
The proved uniform diagonal approximation and the exact successor-mesh
integration theorem give its squared integral. The finite squared sum
is exactly the original energy, and subtype Lebesgue integration gives
the unchanged original c_star normalization. -/
theorem target_energy_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ => (targetChain a b ha hb n).energy/((n:ℝ)+1)^3) atTop
      (𝓝 (persymmetricConstant a ha)) := by
  -- Physical clipping is used only to apply the existing real-line mesh theorem.
  let P : ℝ→Interval := Set.projIcc 0 1 (by norm_num)
  let f (t:ℝ) := persymmetricProfile a ha (P t)
  have hf : Continuous f := (persymmetricProfile a ha).continuous.comp continuous_projIcc
  have hsample (n:ℕ) (i:Fin (n+1)) : f ((i.val:ℝ)/((n:ℝ)+1))=
      persymmetricProfile a ha (matrixPoint n i) := by
    change persymmetricProfile a ha (P ((matrixPoint n i):ℝ))=_
    rw [show P ((matrixPoint n i):ℝ)=matrixPoint n i from
      Set.projIcc_of_mem (by norm_num) (matrixPoint n i).property]
  have hh := successor_mesh_square_integral (fun n i => scaledTargetGreen a b ha hb n i i) f hf (by
    intro ε hε
    obtain ⟨N,hN⟩ := scaledTargetDiagonal_uniform ha hb ε hε
    refine ⟨N,fun n hn i => ?_⟩
    rw [hsample]
    exact hN n hn i)
  -- The exact finite energy identity retains every one of the original N cells.
  have hfinite (n:ℕ) : (∑i:Fin (n+1),(scaledTargetGreen a b ha hb n i i)^2)/((n:ℝ)+1)=
      (targetChain a b ha hb n).energy/((n:ℝ)+1)^3 := by
    simp only [scaledTargetGreen,div_pow]
    rw [← Finset.sum_div]
    change _=(∑i:Fin (n+1),((targetChain a b ha hb n).green i i)^2)/((n:ℝ)+1)^3
    field_simp
  have hint : (∫t in (0:ℝ)..1,(f t)^2)=persymmetricConstant a ha := by
    have hs : persymmetricConstant a ha=∫t:Interval,(f (t:ℝ))^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only [f]
        rw [show P (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property])
    rw [hs,integral_subtype (s:=Icc (0:ℝ) 1) measurableSet_Icc (fun t:ℝ => (f t)^2),
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  simp_rw [hfinite,hint] at hh
  exact hh

/-- The printed actual target diagonal converges to the original
alpha-only profile at every exact interior floor row.
Use: together with the full diagonal bound and target_energy_limit,
this is the complete profile and energy assertion of Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: specialize the proved genuine moving-row diagonal limit at
the original finite floor row and its actual matrix-size mesh limit. -/
theorem target_diagonal_floor_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n:ℕ => scaledTargetGreen a b ha hb n
      (floorMatrixIndex n t ht) (floorMatrixIndex n t ht)) atTop
      (𝓝 (persymmetricProfile a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩)) :=
  scaledTargetDiagonal_limit ha hb id tendsto_id (fun n => floorMatrixIndex n t ht)
    (floorMatrixMesh_tendsto t ht)

end
end jacobi.Comparison
