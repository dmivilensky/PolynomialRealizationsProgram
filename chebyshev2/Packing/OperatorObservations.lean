import chebyshev2.Packing.SpectralTransfer
import chebyshev2.Continuum.KernelSquareIntegral
import chebyshev2.Continuum.Fredholm

/-!
Article: chebyshev2, Theorem 2.4.
Equation (9), with the square-trace observation written as the article's literal double integral.
Result: `chebyshev2.Packing.packed_square_integral_distance` supplies the stated article
conclusion.
-/
namespace chebyshev2.Packing
noncomputable section
open chebyshev2.Continuum MeasureTheory Real
open scoped InnerProductSpace BigOperators

variable {N : ℕ} (J : chebyshev2.Jacobi N)

/--
Defines `packedKernelOperator` of type `FeatureSpace →L[ℝ] FeatureSpace` by `kernelOperator
((packing J hN ht).blocks hN).closedDensity_integrable ((packing J hN ht).blocks
hN).closedDensity_nonneg`.

Use: `chebyshev2.Packing.packedKernel_hasSum_square_trace` uses this definition to
establish the value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i)
((packedKernelOperator J hN ht ∘L packedKernelOperator J hN ht) (b i))) (∑' j, packedEigenvalue
J hN ht j^2)`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packedKernel_hasSum_square_trace`.
-/
def packedKernelOperator (hN : 0 < N) (ht : J.Terminal) : FeatureSpace →L[ℝ] FeatureSpace :=
  kernelOperator ((packing J hN ht).blocks hN).closedDensity_integrable
    ((packing J hN ht).blocks hN).closedDensity_nonneg

/--
The determinant bound applies to the actual convergent Fredholm product.

The stated quantitative bound `|log (fredholmDeterminant (packedEigenvalue J hN ht) s)-log
(cosh (sqrt s))| ≤ s/2*transferError N`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.4.

Proof: Use the identities/estimates `chebyshev2.Continuum.log_fredholmDeterminant`,
`chebyshev2.Packing.packedEigenvalue_summable`,
`chebyshev2.Packing.packedEigenvalue_nonneg` with the arguments shown in the proof.
-/
theorem packed_fredholm_observation_distance (hN : 0 < N) (ht : J.Terminal) {s : ℝ} (hs : 0 ≤ s) :
    |log (fredholmDeterminant (packedEigenvalue J hN ht) s)-log (cosh (sqrt s))| ≤ s/2*transferError N := by
  rw [log_fredholmDeterminant (packedEigenvalue_summable J hN ht) (packedEigenvalue_nonneg J hN ht) hs]
  exact packed_logDeterminant_distance J hN ht hs

/--
The quadratic observation is the trace of the actual squared integral operator in every Hilbert
basis.

The value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i) ((packedKernelOperator
J hN ht ∘L packedKernelOperator J hN ht) (b i))) (∑' j, packedEigenvalue J hN ht j^2)`.

Use: `chebyshev2.Packing.packedKernel_square_trace_distance` rewrites with this
infinite-sum formula to prove the bound `|(∑' i, inner ℝ (b i)
((packedKernelOperator J hN ht ∘L packedKernelOperator J hN ht) (b i)))-(2/3 : ℝ)| ≤
2*transferError N`.

Article: chebyshev2, Theorem 2.4.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.closedDensity_integrable`,
`chebyshev2.Packing.Blocks.closedDensity_nonneg`,
`chebyshev2.Continuum.PositiveSpectralData.hasSum_square_trace` with the arguments shown in
the proof.
-/
theorem packedKernel_hasSum_square_trace (hN : 0 < N) (ht : J.Terminal) {ι : Type*}
    (b : HilbertBasis ι ℝ FeatureSpace) :
    HasSum (fun i => inner ℝ (b i) ((packedKernelOperator J hN ht ∘L packedKernelOperator J hN ht) (b i)))
      (∑' j, packedEigenvalue J hN ht j^2) := by
  -- Use the identities/estimates `chebyshev2.Packing.Blocks.closedDensity_integrable`,
  -- `chebyshev2.Packing.Blocks.closedDensity_nonneg`,
  -- `chebyshev2.Continuum.PositiveSpectralData.hasSum_square_trace` with the arguments
  -- shown in the proof.
  let D := kernelSpectralData ((packing J hN ht).blocks hN).closedDensity_integrable
    ((packing J hN ht).blocks hN).closedDensity_nonneg
  apply D.hasSum_square_trace
  rw [← D.eigenvalue_tsum]
  exact packedEigenvalue_mass J hN ht

/--
The stated quantitative bound `|(∑' i, inner ℝ (b i) ((packedKernelOperator J hN ht ∘L
packedKernelOperator J hN ht) (b i)))-(2/3 : ℝ)| ≤ 2*transferError N`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 2.4.

Proof: Use the identities/estimates `chebyshev2.Packing.packedKernel_hasSum_square_trace`,
`chebyshev2.Packing.packed_square_trace_distance` with the arguments shown in the proof.
-/
theorem packedKernel_square_trace_distance (hN : 0 < N) (ht : J.Terminal) {ι : Type*}
    (b : HilbertBasis ι ℝ FeatureSpace) :
    |(∑' i, inner ℝ (b i) ((packedKernelOperator J hN ht ∘L packedKernelOperator J hN ht) (b i)))-(2/3 : ℝ)| ≤
      2*transferError N := by
  rw [(packedKernel_hasSum_square_trace J hN ht b).tsum_eq]
  exact packed_square_trace_distance J hN ht


/--
Equation (9), with the square-trace observation written as the article's literal double
integral.

The stated quantitative bound `|(∫ x, ∫ y, packedDensity J hN ht x*packedDensity J hN ht y*exp
(-2*|x-y|))-(2/3:ℝ)| ≤ 2*transferError N`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.4.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.closedDensity_integrable`,
`chebyshev2.Packing.Blocks.closedDensity_nonneg`,
`chebyshev2.Continuum.kernelEigenvalue_square_integral` with the arguments shown in the
proof.
-/
theorem packed_square_integral_distance (hN : 0 < N) (ht : J.Terminal) :
    |(∫ x, ∫ y, packedDensity J hN ht x*packedDensity J hN ht y*exp (-2*|x-y|))-(2/3:ℝ)| ≤
      2*transferError N := by
  -- Use the identities/estimates `chebyshev2.Packing.Blocks.closedDensity_integrable`,
  -- `chebyshev2.Packing.Blocks.closedDensity_nonneg`,
  -- `chebyshev2.Continuum.kernelEigenvalue_square_integral` with the arguments shown in
  -- the proof.
  have he := kernelEigenvalue_square_integral
    ((packing J hN ht).blocks hN).closedDensity_integrable
    ((packing J hN ht).blocks hN).closedDensity_nonneg
  change (∑' j, packedEigenvalue J hN ht j^2) =
    (∫ x, ∫ y, packedDensity J hN ht x*packedDensity J hN ht y*exp (-2*|x-y|)) at he
  rw [← he]
  exact packed_square_trace_distance J hN ht

end
end chebyshev2.Packing
