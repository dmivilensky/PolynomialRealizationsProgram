import jacobi.Comparison.CholeskyQuadrature
import jacobi.Comparison.TwoEdgeCholeskyResidual
import jacobi.Support.TargetEdgeUniform

/-!
Article: jacobi, Proposition C.3.
The two actual continuum transformation kernels act on the same genuine
fixed-edge reference wave. The original same-edge sum tends to its
physical transformation integral; the opposite-edge sum vanishes by
uniform alternating cancellation, with its original parity retained.
Use: the actual target polynomial Schur transform uses these same values.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Support jacobi.Finite
open scoped Topology
attribute [local irreducible] kernel transformationKernel

/-- The genuine degree-normalized support polynomial at the fixed
original target edge, defined at every actual physical coordinate.
Use: the actual target polynomial Schur transform uses these same values.
Article: jacobi, Proposition C.3.
-/
def supportEdgeValue (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (i:Fin (n+1)) : ℝ :=
  (n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb n i).eval
    (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k))

/-- The actual reference edge profile with its original Gamma amplitude.
Use: the genuine preceding-row polynomial values are replaced uniformly
by this same continuous profile in the eigenvector limit.
Article: jacobi, Proposition C.3.
-/
def referenceEdgeProfile (a b:ℝ) (ha:-1<a) (k:ℕ) : C(HalfInterval,ℝ) where
  toFun t := (topConstant a b*π^gamma a)*realSolution a (jacobi.Bessel.sigma a ha k) (t:ℝ)
  continuous_toFun := continuous_const.mul (continuous_iff_continuousAt.mpr (fun t =>
    (realSolution_continuousAt ha _ t.property).comp continuous_subtype_val.continuousAt))

/-- The genuine reference profile at a physical matrix sample has
exactly the original source spatial coordinate.
Use: the actual uniform support edge error is the reference-profile
error in the genuine target Schur row approximation.
Article: jacobi, Proposition C.3.
Proof: physical half clipping fixes the original matrix coordinate. -/
theorem referenceEdgeProfile_sample (a b:ℝ) (ha:-1<a) (k:ℕ)
    {n:ℕ} (i:Fin (n+1)) (hi:2*i.val≤n+1) :
    referenceEdgeProfile a b ha k (matrixHalfPoint n i)=
      (topConstant a b*π^gamma a)*realSolution a (jacobi.Bessel.sigma a ha k) (matrixMesh n i) := by
  have he : matrixHalfPoint n i=(⟨matrixMesh n i,matrixMesh_mem_half hi⟩:HalfInterval) :=
    Set.projIcc_of_mem (by norm_num) (matrixMesh_mem_half hi)
  rw [he]
  rfl

/-- The genuine original transformation kernel of order d multiplied
by the actual reference edge profile of the target order a.
Use: ordinary and alternating compact-family quadratures give the two
actual edge contributions to the target polynomial Schur transform.
Article: jacobi, Proposition C.3.
-/
def edgeTransformationProduct (a b d:ℝ) (ha:-1<a) (hd:-1<d) (k:ℕ) :
    C(HalfInterval×HalfInterval,ℝ) where
  toFun p := transformationKernel d hd p.1 p.2*referenceEdgeProfile a b ha k p.2
  continuous_toFun := (transformationKernel_continuous d hd).mul
    ((referenceEdgeProfile a b ha k).continuous.comp continuous_snd)

/-- The genuine two-edge sampled transformation applied to the fixed
original reference profile on the complete actual preceding-row prefix.
Use: the actual target polynomial row is uniformly approximated by this
sum using the proved Cholesky and support-wave limits.
Article: jacobi, Proposition C.3.
-/
def eigenvectorModelRow (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (i:Fin (n+1)) : ℝ :=
  (∑j:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i j)*
    referenceEdgeProfile a b ha k (matrixHalfPoint n (Gram.before i j)))/((n:ℝ)+1)

/-- The exact original two-edge model row is its same-edge Riemann sum
plus its opposite-edge alternating sum with the true row parity.
Use: eigenvectorModelRow_limit identifies the same actual finite sum
with the original transformation integral and proves cancellation.
Article: jacobi, Proposition C.3.
Proof: expand the actual two-edge kernel and split its true parity
into the row and preceding-coordinate factors. Finite sum linearity
retains every original term and its actual prefix length. -/
theorem eigenvectorModelRow_expansion (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n k:ℕ) (i:Fin (n+1)) :
    eigenvectorModelRow a b ha hb n k i =
      (∑j∈Finset.range i.val,edgeTransformationProduct a b a ha ha k
        (matrixHalfPoint n i,halfParameterClamp ((j:ℝ)/((n:ℝ)+1))))/((n:ℝ)+1)+
      (-1:ℝ)^i.val*((∑j∈Finset.range i.val,(-1:ℝ)^j*edgeTransformationProduct a b b ha hb k
        (matrixHalfPoint n i,halfParameterClamp ((j:ℝ)/((n:ℝ)+1))))/((n:ℝ)+1)) := by
  -- The exact within-row parity gives the alternating cross-edge term.
  have he (j:Fin i.val) : twoEdgeTransformation a b ha hb n i (Gram.before i j)*
      referenceEdgeProfile a b ha k (matrixHalfPoint n (Gram.before i j)) =
      edgeTransformationProduct a b a ha ha k
        (matrixHalfPoint n i,halfParameterClamp ((j.val:ℝ)/((n:ℝ)+1)))+
      (-1:ℝ)^i.val*((-1:ℝ)^j.val*edgeTransformationProduct a b b ha hb k
        (matrixHalfPoint n i,halfParameterClamp ((j.val:ℝ)/((n:ℝ)+1)))) := by
    simp only [twoEdgeTransformation,edgeTransformationProduct,ContinuousMap.coe_mk,
      matrixHalfPoint,matrixMesh,Gram.before,pow_add]
    ring
  unfold eigenvectorModelRow
  simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j:ℕ => (-1:ℝ)^j*edgeTransformationProduct a b b ha hb k
    (matrixHalfPoint n i,halfParameterClamp ((j:ℝ)/((n:ℝ)+1)))) i.val]
  rw [Fin.sum_univ_eq_sum_range (fun j:ℕ => edgeTransformationProduct a b a ha ha k
    (matrixHalfPoint n i,halfParameterClamp ((j:ℝ)/((n:ℝ)+1)))) i.val]
  ring

/-- The actual reference-profile model row tends to its original
same-edge GL transformation integral along every cofinal physical row.
Use: the genuine target Schur row limit is identified with the actual
transformed solution after its two uniform approximation errors vanish.
Article: jacobi, Proposition C.3.
Proof: compact-family quadrature gives the actual same-edge integral.
The full opposite-edge alternating prefix sum tends uniformly to zero;
its unchanged actual row parity has absolute one. Add the two limits
using the exact finite row expansion. -/
theorem eigenvectorModelRow_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun r => eigenvectorModelRow a b ha hb (ns r) k (i r)) atTop
      (𝓝 (∫s in (0:ℝ)..t, edgeTransformationProduct a b a ha ha k
        (⟨t,ht⟩,halfParameterClamp s))) := by
  -- Both actual sums use the original matrix dimension ns+1, not the degree ns.
  have hn : Tendsto (fun r => ns r+1) atTop atTop := tendsto_atTop_mono (fun _ => Nat.le_succ _) hns
  have hA := compact_prefix_mesh_limit (edgeTransformationProduct a b a ha ha k)
    (fun r => matrixHalfPoint (ns r) (i r)) (matrixHalfPoint_limit ns hns i ht hit)
    (fun r => ns r+1) (fun r => (i r).val) hn
    (Eventually.of_forall (fun r => (i r).isLt.le))
    (show t∈Icc (0:ℝ) 1 from ⟨ht.1,ht.2.trans (by norm_num)⟩)
    (by simpa only [Nat.cast_add,Nat.cast_one] using degree_to_size_mesh (m:=fun r => (i r).val) hns hit)
  have hB : Tendsto (fun r => (-1:ℝ)^(i r).val*
      ((∑j∈Finset.range (i r).val,(-1:ℝ)^j*edgeTransformationProduct a b b ha hb k
        (matrixHalfPoint (ns r) (i r),halfParameterClamp ((j:ℝ)/((ns r:ℝ)+1))))/((ns r:ℝ)+1))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := compact_alternating_mesh_zero (edgeTransformationProduct a b b ha hb k) ε hε
    filter_upwards [hn.eventually_ge_atTop N] with r hr
    have hh := hN (ns r+1) hr (i r).val (i r).isLt.le (matrixHalfPoint (ns r) (i r))
    simpa only [Real.dist_eq,sub_zero,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      Nat.cast_add,Nat.cast_one] using hh
  have hh := hA.add hB
  simp only [add_zero,Nat.cast_add,Nat.cast_one] at hh
  simpa only [eigenvectorModelRow_expansion] using hh

end
end jacobi.Comparison
