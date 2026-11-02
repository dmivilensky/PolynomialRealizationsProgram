import krylov.Correction.ConstantBounds
import krylov.LinearAlgebra.Aggregation
import krylov.LinearAlgebra.FrobeniusAggregation

/-!
Article: main_krylov, thm:C and thm:C2(a), the sharp second-order compression bound.
Use: apply the scalar constant to actual selfadjoint increments and actual
orthogonal old-subspace compressions, with the two norm conventions separate.
Source: reuse the proved spectral and Frobenius aggregated compression inequalities.
-/

namespace krylov.Correction
noncomputable section
open Finset krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual compressed second-order residual satisfies the sharp spectral-budget bound.
Use: supplies the operator inequality in thm:C, including empty and zero-budget profiles.
Article: main_krylov, thm:C, ‖𝓛 f̂‖≤K(W₀,w′).
Proof: retain the correlated square-root loss from the existing aggregated
compression theorem, add the actual final-operator action and maximize the scalar parameter. -/
theorem spectral_compression_bound (I : Finset ι) (K : ι → Submodule ℝ E)
    [∀ i, (K i).HasOrthogonalProjection] (T : ι → E →L[ℝ] E)
    (hT : ∀ i ∈ I, IsSelfAdjoint (T i)) (ω : ι → ℝ)
    (hω : ∀ i ∈ I, ‖T i‖ ≤ ω i) (h : E)
    (hh : ∀ i ∈ I, h ∈ (K i)ᗮ) (hn : ‖h‖=1)
    (F : E →L[ℝ] E) {w : ℝ} (hF : ‖F‖ ≤ w) :
    let X := ∑ i ∈ I, (K i).starProjection (T i h)
    ‖(∑ i ∈ I, (K i).starProjection (T i ((K i).starProjection X)))+F X‖ ≤
      sharpConstant (∑ i ∈ I, ω i) w := by
  -- Retain the cross/compression correlation before adding the final operator action.
  let X := ∑ i ∈ I, (K i).starProjection (T i h)
  have ha := aggregated_compression_action I K T hT ω hω h hh hn
  have hW : 0 ≤ ∑ i ∈ I, ω i := sum_nonneg fun i hi => (norm_nonneg _).trans (hω i hi)
  have hw : 0 ≤ w := (norm_nonneg F).trans hF
  have hFx : ‖F X‖ ≤ w*‖X‖ := (F.le_opNorm X).trans
    (mul_le_mul_of_nonneg_right hF (norm_nonneg X))
  exact (norm_add_le _ _).trans ((add_le_add ha.2 hFx).trans
    ((by ring_nf : ‖X‖*Real.sqrt ((∑ i ∈ I, ω i)^2-‖X‖^2)+w*‖X‖ =
      ‖X‖*(Real.sqrt ((∑ i ∈ I, ω i)^2-‖X‖^2)+w)).le.trans
        (compression_scalar_bound hW hw (norm_nonneg X) ha.1)))

/-- Frobenius increment budgets improve the actual second-order bound by √2.
Use: supplies the norm-sensitive upper bound in thm:C2(a) for actual matrices.
Article: main_krylov, thm:C2(a), √2‖𝓛 f̂‖≤K(W₀,w′).
Proof: the proved Frobenius aggregate bound uses √2‖X‖ as its scalar cross
parameter; multiply the actual residual estimate by √2 and apply the same scalar maximum. -/
theorem frobenius_compression_bound {n : ℕ} (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (D : ι → Matrix (Fin n) (Fin n) ℝ) (hD : ∀ i ∈ I, (D i).IsSymm)
    (ω : ι → ℝ) (hω : ∀ i ∈ I, chebyshev1.hsNorm (D i) ≤ ω i)
    (h : EuclideanSpace ℝ (Fin n)) (hh : ∀ i ∈ I, h ∈ (K i)ᗮ) (hn : ‖h‖=1)
    (F : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {w : ℝ} (hF : ‖F‖ ≤ w) :
    let T := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (D i)
    let X := ∑ i ∈ I, (K i).starProjection (T i h)
    Real.sqrt 2 * ‖(∑ i ∈ I, (K i).starProjection (T i ((K i).starProjection X)))+F X‖ ≤
      sharpConstant (∑ i ∈ I, ω i) w := by
  -- Use the twice-counted symmetric cross energy as the scalar maximizing parameter.
  let T := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (D i)
  let X := ∑ i ∈ I, (K i).starProjection (T i h)
  have ha := frobenius_aggregated_compression I K D hD ω hω h hh hn
  have hW : 0 ≤ ∑ i ∈ I, ω i :=
    sum_nonneg fun i hi => (chebyshev1.hsNorm_nonneg _).trans (hω i hi)
  have hw : 0 ≤ w := (norm_nonneg F).trans hF
  have hFx : ‖F X‖ ≤ w*‖X‖ := (F.le_opNorm X).trans
    (mul_le_mul_of_nonneg_right hF (norm_nonneg X))
  have hb := mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ha.2 hFx))
    (Real.sqrt_nonneg 2)
  have hm := compression_scalar_bound hW hw
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg X)) ha.1
  have hs : (Real.sqrt 2 * ‖X‖)^2=2*‖X‖^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs] at hm
  exact hb.trans ((by ring : Real.sqrt 2 *
    (‖X‖*Real.sqrt ((∑ i ∈ I, ω i)^2-2*‖X‖^2)+w*‖X‖) =
    (Real.sqrt 2*‖X‖)*(Real.sqrt ((∑ i ∈ I, ω i)^2-2*‖X‖^2)+w)).le.trans hm)

end
end krylov.Correction
