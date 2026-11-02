import jacobi.Comparison.Model
import jacobi.Finite.GapWeights

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The actual target and corrected support probabilities obey precisely
the printed relative-gap-product formula. Both positive normalizers
refer to the existing original spectral measures; the corrected support
nodes are allowed to lie outside the contractive interval.
Use: comparisonWeight_ratio and comparisonGap_log_majorant compare the actual target and support probabilities through this same original finite product.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset jacobi.Finite jacobi.Support

/-- The article's literal finite relative product of the corrected support gaps and genuine target gaps.
Use: comparisonWeight_ratio and comparisonGap_log_majorant compare the actual target and support probabilities through this same original finite product.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def relativeGapProduct (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) : ℝ :=
  ∏j∈univ.erase k,
    |jacobi.Jacobi.modelNode a b (n+1) k.val- jacobi.Jacobi.modelNode a b (n+1) j.val|/
      |(jacobi.Jacobi.nodes a b ha hb (n+1)).value k-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j|

/-- The original relative product is the quotient of the exact two original characteristic-gap products.
Use: relativeGapProduct_pos and comparisonWeight_ratio keep the same original spectral factors and normalization as the source formula.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: finite products distribute over division, with the same original omitted diagonal on both sides. -/
theorem relativeGapProduct_eq (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    relativeGapProduct a b ha hb n k=
      gapProduct (fun j:Fin (n+1) => jacobi.Jacobi.modelNode a b (n+1) j.val) k/
        gapProduct (jacobi.Jacobi.nodes a b ha hb (n+1)).value k := prod_div_distrib _ _

/-- The actual corrected support probabilities equal the genuine normalized inverse gaps at those same original corrected nodes.
Use: comparisonWeight_ratio applies the already proved finite normalized-gap comparison to the actual support measure, without assuming a second canonical reconstruction.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the genuine natural support probabilities have the independently proved inverse-characteristic-derivative formula. Their exact gap probabilities are invariant under the same original positive affine correction, which keeps the actual support eigenvectors and probabilities unchanged. -/
theorem supportMeasure_gapWeight (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    (supportMeasure a b ha hb n).weight k=
      gapWeight (fun j:Fin (n+1) => jacobi.Jacobi.modelNode a b (n+1) j.val) k := by
  change (naturalNodes a b ha hb (n+1)).persymmetricWeights.val k=_
  rw [Nodes.persymmetricWeights_gap]
  have h := gapWeight_affine (naturalNodes a b ha hb (n+1)).value
    (modelScale_pos ha hb (show 0<n+1 by omega)).ne' (jacobi.Jacobi.modelShift a b (n+1)) k
  exact h.symm

/-- The actual target probabilities equal the genuine normalized inverse characteristic gaps at the original Jacobi zeros.
Use: comparisonWeight_ratio concerns precisely the canonical target matrix used in Theorems A–B, rather than a comparison probability family.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the existing actual target measure is the canonical persymmetric reconstruction at the genuine Jacobi nodes; its already proved absolute derivative rule is exactly the gap probability formula. -/
theorem targetMeasure_gapWeight (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    (targetMeasure a b ha hb n).weight k=gapWeight (jacobi.Jacobi.nodes a b ha hb (n+1)).value k :=
  (jacobi.Jacobi.nodes a b ha hb (n+1)).persymmetricWeights_gap k

/-- Every original finite relative gap product is strictly positive.
Use: the exact probability normalization and the logarithmic relative-gap estimates use genuine positive original quantities.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the corrected support nodes and genuine target nodes are both independently proved distinct, so both original complete absolute-gap products are positive. -/
theorem relativeGapProduct_pos (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    0<relativeGapProduct a b ha hb n k := by
  rw [relativeGapProduct_eq]
  exact div_pos (gapProduct_pos (correctedNodes_injective ha hb (by omega)) k)
    (gapProduct_pos (jacobi.Jacobi.nodes a b ha hb (n+1)).strictAnti.injective k)

/-- The actual target/support probability ratio has precisely the original weighted relative-gap normalization.
Use: the quantitative weight-ratio estimates, the two-edge Gram limit and the eventual target eigenvector normalization all start from this exact identity for the original matrices.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: identify both original measures with their actual normalized inverse characteristic gaps. Apply the proved finite positive-gap reweighting identity and restore the same literal original relative product in every finite summand. -/
theorem comparisonWeight_ratio (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    (targetMeasure a b ha hb n).weight k/(supportMeasure a b ha hb n).weight k=
      relativeGapProduct a b ha hb n k/
        (∑j,(supportMeasure a b ha hb n).weight j*relativeGapProduct a b ha hb n j) := by
  simp only [targetMeasure_gapWeight,supportMeasure_gapWeight,relativeGapProduct_eq]
  exact gapWeight_ratio (jacobi.Jacobi.nodes a b ha hb (n+1)).strictAnti.injective
    (correctedNodes_injective ha hb (by omega)) k

end
end jacobi.Comparison
