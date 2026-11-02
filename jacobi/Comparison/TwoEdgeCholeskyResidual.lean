import jacobi.Comparison.CholeskyDiagonalResidual
import jacobi.Finite.SchurGram

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
The true two-edge sampled transformation kernel solves the discrete
two-edge GL equation up to a uniformly vanishing residual. Its two
same-edge terms cancel by the actual GL equations and its two mixed
terms vanish by the proved uniform alternating mesh cancellation.
Use: the full Cholesky coefficient limit compares N*c_ij with these genuine original transformation kernels.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Finite
open scoped Topology
attribute [local irreducible] kernel transformationKernel

/-- The actual sampled two-edge transformation kernel with the source
alternating second-edge sign.
Use: the full Cholesky coefficient limit compares N*c_ij with these
genuine original transformation kernels.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def twoEdgeTransformation (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  transformationKernel a ha (matrixHalfPoint n i) (matrixHalfPoint n j)+
    (-1:ℝ)^(i.val+j.val)*transformationKernel b hb (matrixHalfPoint n i) (matrixHalfPoint n j)

/-- The actual sampled two-edge original GL kernel, on the same physical
coordinates and with the same parity as the sampled transformation.
Use: twoEdgeModelResidual is the literal discretized source GL equation.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def twoEdgeKernel (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  kernel a ha (matrixHalfPoint n i:ℝ) (matrixHalfPoint n j:ℝ)+
    (-1:ℝ)^(i.val+j.val)*kernel b hb (matrixHalfPoint n i:ℝ) (matrixHalfPoint n j:ℝ)

/-- The exact mixed original kernel product at an actual preceding-row
mesh coordinate.
Use: the full two-edge residual expansion retains both nonalternating
and alternating original kernel-product sums explicitly.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def glMeshTerm (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) (l:ℕ) : ℝ :=
  transformationProduct a b ha hb ((matrixHalfPoint n i,matrixHalfPoint n j),
    halfParameterClamp ((l:ℝ)/((n:ℝ)+1)))

/-- The literal discretized two-edge GL residual using the actual
original preceding-row prefix and matrix-size factor.
Use: twoEdgeModelResidual_uniform supplies the full source quadrature
error before replacement by the actual finite Gram entries.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def twoEdgeModelResidual (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  twoEdgeTransformation a b ha hb n i j+twoEdgeKernel a b ha hb n i j+
    (∑ l:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i l)*
      twoEdgeKernel a b ha hb n (Gram.before i l) j)/((n:ℝ)+1)

/-- The exact finite two-edge residual splits into the two actual
same-edge residuals and the two original alternating cross-edge sums.
Use: twoEdgeModelResidual_uniform proves the source's complete uniform
quadrature cancellation, retaining all four terms and their true signs.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: expand each genuine finite product. The internal parity has
square one; finite sum linearity then separates exactly the four actual
kernel products, with no parity averaging or omitted endpoint term. -/
theorem twoEdgeModelResidual_expansion (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i j:Fin (n+1)) :
    twoEdgeModelResidual a b ha hb n i j =
      sameEdgeResidual a ha n i j+(-1:ℝ)^(i.val+j.val)*sameEdgeResidual b hb n i j+
      (-1:ℝ)^j.val*((∑l∈Finset.range i.val, (-1:ℝ)^l*glMeshTerm a b ha hb n i j l)/((n:ℝ)+1))+
      (-1:ℝ)^i.val*((∑l∈Finset.range i.val, (-1:ℝ)^l*glMeshTerm b a hb ha n i j l)/((n:ℝ)+1)) := by
  -- Retain the internal parity until its exact square-one identity separates all four products.
  have hprod (l:Fin i.val) :
      twoEdgeTransformation a b ha hb n i (Gram.before i l)*
      twoEdgeKernel a b ha hb n (Gram.before i l) j =
      glMeshTerm a a ha ha n i j l.val+
      (-1:ℝ)^(i.val+j.val)*glMeshTerm b b hb hb n i j l.val+
      (-1:ℝ)^j.val*((-1:ℝ)^l.val*glMeshTerm a b ha hb n i j l.val)+
      (-1:ℝ)^i.val*((-1:ℝ)^l.val*glMeshTerm b a hb ha n i j l.val) := by
    have hsign : (-1:ℝ)^l.val*(-1:ℝ)^l.val=1 := by rw [← mul_pow]; norm_num
    simp only [twoEdgeTransformation,twoEdgeKernel,glMeshTerm,transformationProduct,
      ContinuousMap.coe_mk,matrixHalfPoint,matrixMesh,Gram.before,pow_add]
    linear_combination
      ((-1:ℝ)^i.val*(-1:ℝ)^j.val*
        transformationKernel b hb (halfParameterClamp ((i.val:ℝ)/((n:ℝ)+1)))
          (halfParameterClamp ((l.val:ℝ)/((n:ℝ)+1)))*
        kernel b hb (halfParameterClamp ((l.val:ℝ)/((n:ℝ)+1)):ℝ)
          (halfParameterClamp ((j.val:ℝ)/((n:ℝ)+1)):ℝ)) * hsign
  unfold twoEdgeModelResidual
  simp_rw [hprod,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun l:ℕ => (-1:ℝ)^l*glMeshTerm a b ha hb n i j l) i.val,
    Fin.sum_univ_eq_sum_range (fun l:ℕ => (-1:ℝ)^l*glMeshTerm b a hb ha n i j l) i.val]
  simp_rw [Fin.sum_univ_eq_sum_range]
  unfold sameEdgeResidual twoEdgeTransformation twoEdgeKernel glMeshTerm
  simp only [pow_add]
  ring

/-- The genuine complete two-edge sampled Cholesky residual vanishes
uniformly over the entire original physical half square.
Use: the original finite Gram residual and the genuine coercive inverse
estimate identify the limit of the actual original Cholesky coefficients.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: use the exact four-term expansion. Both actual same-edge terms
vanish uniformly by the source GL equations, both mixed terms by the
proved compact-family alternating cancellation. Every remaining parity
factor has absolute value exactly one. -/
theorem twoEdgeModelResidual_uniform (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i j:Fin (n+1),
      2*i.val≤n+1 → 2*j.val≤n+1 → |twoEdgeModelResidual a b ha hb n i j|<ε := by
  -- Use the independently proved same-edge and alternating bounds at the same tolerance.
  intro ε hε
  obtain ⟨NA,hA⟩ := sameEdgeResidual_uniform a ha (ε/4) (by positivity)
  obtain ⟨NB,hB⟩ := sameEdgeResidual_uniform b hb (ε/4) (by positivity)
  obtain ⟨NC,hC⟩ := transformationProduct_alternating_zero a b ha hb (ε/4) (by positivity)
  obtain ⟨ND,hD⟩ := transformationProduct_alternating_zero b a hb ha (ε/4) (by positivity)
  refine ⟨max (max NA NB) (max NC ND),fun n hn i j hi hj => ?_⟩
  have hAn := hA n (by omega) i j hi hj
  have hBn := hB n (by omega) i j hi hj
  have hCn := hC n (by omega) i j
  have hDn := hD n (by omega) i j
  change |(∑l∈Finset.range i.val,(-1:ℝ)^l*glMeshTerm a b ha hb n i j l)/((n:ℝ)+1)|<ε/4 at hCn
  change |(∑l∈Finset.range i.val,(-1:ℝ)^l*glMeshTerm b a hb ha n i j l)/((n:ℝ)+1)|<ε/4 at hDn
  rw [twoEdgeModelResidual_expansion]
  have hh := (abs_add_le
    (sameEdgeResidual a ha n i j+(-1:ℝ)^(i.val+j.val)*sameEdgeResidual b hb n i j+
      (-1:ℝ)^j.val*((∑l∈Finset.range i.val,(-1:ℝ)^l*glMeshTerm a b ha hb n i j l)/((n:ℝ)+1)))
    ((-1:ℝ)^i.val*((∑l∈Finset.range i.val,(-1:ℝ)^l*glMeshTerm b a hb ha n i j l)/((n:ℝ)+1)))).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] at hh
  exact hh.trans_lt (by change |sameEdgeResidual a ha n i j|+|sameEdgeResidual b hb n i j|+_+_<ε; linarith)

end
end jacobi.Comparison
