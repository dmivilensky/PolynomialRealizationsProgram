import jacobi.Analysis.CompactPrefixMesh
import jacobi.Analysis.CompactAlternatingMesh
import jacobi.Analysis.HalfMatrixCompactness
import jacobi.GelfandLevitan.KernelRowEquation

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
The actual GL kernel products have their moving-prefix Riemann limits;
their alternating cross-edge sums vanish uniformly. The exact source GL
equation consequently cancels the complete same-edge discrete residual.
Use: the actual sampled GL kernels and their finite quadrature use one continuous physical coordinate map, also at the original midpoint.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel transformationKernel

/-- Original matrix-size coordinate in the physical half interval.
Use: the actual sampled GL kernels and their finite quadrature use one
continuous physical coordinate map, also at the original midpoint.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def matrixHalfPoint (n:ℕ) (i:Fin (n+1)) : HalfInterval :=
  halfParameterClamp (matrixMesh n i)

/-- The actual mixed original GL product as one compact continuous
family, parametrized by its two physical endpoint coordinates.
Use: ordinary same-edge and alternating cross-edge quadratures use
the same genuine K and F as the original source GL equation.
Article: jacobi, Proposition C.3.
-/
def transformationProduct (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    C((HalfInterval×HalfInterval)×HalfInterval,ℝ) where
  toFun p := transformationKernel a ha p.1.1 p.2*kernel b hb (p.2:ℝ) (p.1.2:ℝ)
  continuous_toFun := by
    have hK : Continuous (fun p:(HalfInterval×HalfInterval)×HalfInterval =>
        transformationKernel a ha p.1.1 p.2) := (transformationKernel_continuous a ha).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hF : Continuous (fun p:(HalfInterval×HalfInterval)×HalfInterval =>
        kernel b hb (p.2:ℝ) (p.1.2:ℝ)) :=
      ContinuousOn.comp_continuous
        (g:=fun p:ℝ × ℝ => kernel b hb p.1 p.2)
        (f:=fun p:(HalfInterval×HalfInterval)×HalfInterval => ((p.2:ℝ),(p.1.2:ℝ)))
        (kernel_continuousOn b hb)
        ((continuous_subtype_val.comp continuous_snd).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
        (fun p => ⟨p.2.property,p.1.2.property⟩)
    exact hK.mul hF

/-- Actual half coordinates of cofinally moving original matrix indices
have their genuine limiting physical point.
Use: transformationProduct_prefix_limit obtains both moving kernel
parameters from the original article's matrix-coordinate convergence.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the original degree and matrix-size coordinates have the same
limit. Continuous physical clipping fixes that genuine half point. -/
theorem matrixHalfPoint_limit (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i:∀r:ℕ,Fin (ns r+1)) {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun r => matrixHalfPoint (ns r) (i r)) atTop (𝓝 (⟨t,ht⟩:HalfInterval)) := by
  have hh := halfParameterClamp.continuous.continuousAt.tendsto.comp
    (degree_to_size_mesh (m:=fun r => (i r).val) hns hit)
  have he : halfParameterClamp t=(⟨t,ht⟩:HalfInterval) := Set.projIcc_of_mem (by norm_num) ht
  rw [he] at hh
  exact hh

/-- Every actual compact GL product has its true moving-prefix spatial
integral limit along all cofinal original physical row-column pairs.
Use: sameEdgeResidual_uniform cancels the genuine original GL equation
in the source Cholesky convergence argument.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the true physical endpoint parameters converge, and the actual
prefix length divided by the original matrix size converges to t.
Apply the established compact-family prefix mesh theorem; all actual
kernel bounds and endpoint hypotheses are already proved. -/
theorem transformationProduct_prefix_limit (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i j:∀r:ℕ,Fin (ns r+1))
    {t s:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 t))
    (hjs:Tendsto (fun r:ℕ => ((j r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun r => (∑ l∈Finset.range (i r).val,
      transformationProduct a b ha hb
        ((matrixHalfPoint (ns r) (i r),matrixHalfPoint (ns r) (j r)),
          halfParameterClamp ((l:ℝ)/((ns r:ℝ)+1))))/((ns r:ℝ)+1)) atTop
      (𝓝 (∫ x in (0:ℝ)..t,
        transformationProduct a b ha hb ((⟨t,ht⟩,⟨s,hs⟩),halfParameterClamp x))) := by
  -- The original matrix-size coordinate supplies both the moving prefix and the kernel parameters.
  have hn : Tendsto (fun r => ns r+1) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) hns
  have hp := (matrixHalfPoint_limit ns hns i ht hit).prodMk_nhds
    (matrixHalfPoint_limit ns hns j hs hjs)
  have hh := compact_prefix_mesh_limit (transformationProduct a b ha hb)
    (fun r => (matrixHalfPoint (ns r) (i r),matrixHalfPoint (ns r) (j r))) hp
    (fun r => ns r+1) (fun r => (i r).val) hn
    (Eventually.of_forall (fun r => (i r).isLt.le))
    (show t∈Icc (0:ℝ) 1 from ⟨ht.1,ht.2.trans (by norm_num)⟩)
    (by simpa only [Nat.cast_add,Nat.cast_one] using degree_to_size_mesh (m:=fun r => (i r).val) hns hit)
  simpa only [Nat.cast_add,Nat.cast_one] using hh

/-- The actual mixed cross-edge GL product has uniformly vanishing
alternating original prefix sums over all physical matrix parameters.
Use: the two opposite-edge terms in the full two-edge Cholesky residual
vanish without a parity subsequence or an extra cancellation assumption.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the actual product is a compact continuous family, so the proved
uniform adjacent-pair cancellation applies to every original prefix. -/
theorem transformationProduct_alternating_zero (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i j:Fin (n+1),
      |(∑ l∈Finset.range i.val, (-1:ℝ)^l*
        transformationProduct a b ha hb ((matrixHalfPoint n i,matrixHalfPoint n j),
          halfParameterClamp ((l:ℝ)/((n:ℝ)+1))))/((n:ℝ)+1)|<ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := compact_alternating_mesh_zero (transformationProduct a b ha hb) ε hε
  refine ⟨N,fun n hn i j => ?_⟩
  simpa only [Nat.cast_add,Nat.cast_one] using
    hN (n+1) (by omega) i.val i.isLt.le (matrixHalfPoint n i,matrixHalfPoint n j)

end
end jacobi.Comparison
