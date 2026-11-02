import jacobi.Finite.Persymmetric

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
Normalized inverse absolute-gap products apply to arbitrary distinct real
nodes, including the corrected support spectrum outside (-1,1). Positive
affine changes preserve these probabilities. The existing characteristic
derivative probabilities agree exactly with this finite product formula.
Source: the reciprocal-derivative rule for persymmetric Jacobi matrices,
already proved in Finite.Persymmetric.
Use: gapWeight expresses the actual target/support probability ratio through the same original node gaps used in Appendix E.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset Polynomial

/-- The absolute product of all genuine spectral gaps from one original node.
Use: gapWeight expresses the actual target/support probability ratio through the same original node gaps used in Appendix E.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def gapProduct {N:ℕ} (x:Fin N→ℝ) (k:Fin N) : ℝ :=
  ∏j∈univ.erase k,|x k-x j|

/-- The normalized inverse-gap probability at an actual finite node.
Use: comparisonWeight_ratio is the literal normalization-free formula of Appendix C.4 for the actual corrected support and target nodes.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def gapWeight {N:ℕ} (x:Fin N→ℝ) (k:Fin N) : ℝ :=
  (gapProduct x k)⁻¹/(∑j,(gapProduct x j)⁻¹)

/-- The actual gap product is strictly positive for every node of a distinct finite family.
Use: all cancellations and probability normalizations in the exact original weight-ratio formula have genuine nonzero denominators.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: each omitted-diagonal factor is the absolute value of a nonzero original spectral gap; the empty product is one. -/
theorem gapProduct_pos {N:ℕ} {x:Fin N→ℝ} (hx:Function.Injective x) (k:Fin N) :
    0<gapProduct x k := by
  apply prod_pos
  intro j hj
  exact abs_pos.mpr (sub_ne_zero.mpr (fun he => (mem_erase.mp hj).1 (hx he).symm))

/-- The inverse-gap normalizer is genuinely positive whenever an actual finite node exists.
Use: gapWeight_ratio compares normalized original probability weights without assuming a separate positive normalizing constant.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: every inverse-gap summand is positive; the supplied genuine node makes the finite summation set nonempty. -/
theorem gapNormalizer_pos {N:ℕ} {x:Fin N→ℝ} (hx:Function.Injective x) (k:Fin N) :
    0<∑j,(gapProduct x j)⁻¹ :=
  sum_pos (fun j _ => inv_pos.mpr (gapProduct_pos hx j)) ⟨k,mem_univ _⟩

/-- The actual canonical characteristic derivative has exactly the original absolute-gap product.
Use: Nodes.persymmetricWeights_gap identifies the existing genuine inverse-spectral construction with the node-product formula used by the target/support comparison.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: construct the already verified uniform-weight reference in the same original fibre and apply its exact characteristic derivative formula at the indexed node. Taking absolute values gives the complete original gap product. -/
theorem Nodes.derivative_gap {n:ℕ} (S:Nodes (n+1)) (k:Fin (n+1)) :
    |S.polynomial.derivative.eval (S.value k)|=gapProduct S.value k := by
  let M := S.measure (uniformWeights n)
  have h := M.reconstructedBasis.charpoly_derivative k
  rw [M.reconstructed_charpoly] at h
  have he : S.polynomial.derivative.eval (S.value k)=∏j∈univ.erase k,(S.value k-S.value j) := h
  rw [he,abs_prod]
  rfl

/-- The original canonical persymmetric probabilities are the exact normalized inverse-gap products.
Use: the original target measure and natural support measure share this same independently proved probability normalization in Appendix C.4.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: substitute the genuine absolute characteristic derivative identity into the existing normalized canonical probabilities, including their original finite normalizer. -/
theorem Nodes.persymmetricWeights_gap {n:ℕ} (S:Nodes (n+1)) (k:Fin (n+1)) :
    S.persymmetricWeights.val k=gapWeight S.value k := by
  change |S.polynomial.derivative.eval (S.value k)|⁻¹/S.derivativeNormalizer=_
  simp only [Nodes.derivativeNormalizer,S.derivative_gap,gapWeight]

/-- A common nonzero affine change multiplies every original gap product by the same exact power.
Use: gapWeight_affine proves that the corrected support nodes retain the original natural probabilities even when their affine image is not contractive.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: each original gap gains the factor c; its absolute value gains |c|. The omitted-diagonal product contains exactly N-1 genuine factors. -/
theorem gapProduct_affine {N:ℕ} (x:Fin N→ℝ) (c d:ℝ) (k:Fin N) :
    gapProduct (fun j => c*x j+d) k=|c|^(N-1)*gapProduct x k := by
  have he (j:Fin N) : c*x k+d-(c*x j+d)=c*(x k-x j) := by ring
  simp only [gapProduct,he,abs_mul,prod_mul_distrib,prod_const,
    card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin]

/-- The normalized original inverse-gap probabilities are invariant under every common nonzero real affine change.
Use: the actual corrected support probabilities are identified with their genuine corrected model-node gap products in comparisonWeight_ratio.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the same nonzero factor |c|^(N-1) multiplies every genuine gap product. Its inverse factors out of the finite normalizing sum and cancels from every original probability. -/
theorem gapWeight_affine {N:ℕ} (x:Fin N→ℝ) {c:ℝ} (hc:c≠0) (d:ℝ) (k:Fin N) :
    gapWeight (fun j => c*x j+d) k=gapWeight x k := by
  simp only [gapWeight,gapProduct_affine,mul_inv_rev]
  rw [← sum_mul]
  have hpow : |c|^(N-1)≠0 := pow_ne_zero _ (abs_ne_zero.mpr hc)
  exact mul_div_mul_right _ _ (inv_ne_zero hpow)

/-- The exact ratio of two original inverse-gap probability families is their relative gap product divided by its original weighted normalizer.
Use: comparisonWeight_ratio specializes this identity to the actual target and corrected support nodes; quantitative logarithm bounds concern that same finite relative product.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: multiply the original support probability by its relative gap product. The support gap cancels pointwise, leaving precisely the target inverse-gap normalizer divided by the support normalizer. Both original normalizers and all original gaps are positive. -/
theorem gapWeight_ratio {N:ℕ} {x y:Fin N→ℝ} (hx:Function.Injective x) (hy:Function.Injective y) (k:Fin N) :
    gapWeight x k/gapWeight y k=(gapProduct y k/gapProduct x k)/
      (∑j,gapWeight y j*(gapProduct y j/gapProduct x j)) := by
  -- Cancel the actual support gap before taking the finite normalizing sum.
  have hsum : (∑j,gapWeight y j*(gapProduct y j/gapProduct x j))=
      (∑j,(gapProduct x j)⁻¹)/(∑j,(gapProduct y j)⁻¹) := by
    rw [sum_div]
    apply sum_congr rfl
    intro j _
    unfold gapWeight
    field_simp [(gapProduct_pos hx j).ne',(gapProduct_pos hy j).ne']
  rw [hsum]
  unfold gapWeight
  field_simp [(gapProduct_pos hx k).ne',(gapProduct_pos hy k).ne',
    (gapNormalizer_pos hx k).ne',(gapNormalizer_pos hy k).ne']

end
end jacobi.Finite
