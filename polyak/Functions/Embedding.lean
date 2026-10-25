import polyak.Functions.Transforms
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Article: dimension extension of genuine objectives in the original class.
Use: add orthogonal coordinates while preserving actual gradients and objective
values on the original subspace. All embeddings preserve the Hilbert norm.
-/

noncomputable section

namespace polyak

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Article: orthogonal restriction to the embedded original space. -/
def embeddingProjection (J : E →ₗᵢ[ℝ] F) : F →L[ℝ] E :=
  J.toContinuousLinearMap.adjoint

/-- Article: orthogonal restriction is the left inverse of the embedding.
Proof: an isometry's adjoint composed with itself is the identity. -/
@[simp] theorem embeddingProjection_embed (J : E →ₗᵢ[ℝ] F) (x : E) :
    embeddingProjection J (J x) = x := by
  exact congrArg (fun T : E →L[ℝ] E => T x) J.adjoint_comp_self

/-- Article: projection cannot enlarge the Hilbert norm.
Proof: the adjoint preserves operator norm and an isometry has operator norm ≤1. -/
theorem norm_embeddingProjection_le (J : E →ₗᵢ[ℝ] F) (x : F) :
    ‖embeddingProjection J x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖embeddingProjection J‖ * ‖x‖ := (embeddingProjection J).le_opNorm x
    _ ≤ 1 * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      change ‖J.toContinuousLinearMap.adjoint‖ ≤ 1
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact J.norm_toContinuousLinearMap_le
    _ = ‖x‖ := one_mul _

/-- Article: normalized potential extended constantly in orthogonal directions. -/
def extendPotential (J : E →ₗᵢ[ℝ] F) (ψ : E → ℝ) : F → ℝ :=
  fun x => ψ (embeddingProjection J x)

/-- Article: the projected potential has a genuine derivative.
Proof: the chain rule and the defining adjoint inner-product identity. -/
theorem hasGradientAt_extendPotential (J : E →ₗᵢ[ℝ] F) {ψ : E → ℝ}
    (hψ : Differentiable ℝ ψ) (x : F) :
    HasGradientAt (extendPotential J ψ) (J (gradient ψ (embeddingProjection J x))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hψ (embeddingProjection J x)).hasGradientAt.hasFDerivAt.comp x
    (embeddingProjection J).hasFDerivAt) using 1
  · rfl
  · ext y
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply]
    exact (ContinuousLinearMap.adjoint_inner_right J.toContinuousLinearMap
      (gradient ψ (embeddingProjection J x)) y).symm

/-- Article: extending the normalized potential preserves its exact class.
Proof: its gradient is an isometric embedding of a nonexpansive projected gradient. -/
theorem NormalizedSmooth.extendPotential (J : E →ₗᵢ[ℝ] F) {ψ : E → ℝ}
    (hψ : NormalizedSmooth ψ) : NormalizedSmooth (polyak.extendPotential J ψ) := by
  have hg := hasGradientAt_extendPotential J hψ.differentiable
  refine ⟨fun x => (hg x).differentiableAt, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    rw [(hg x).gradient, (hg y).gradient, ← map_sub, J.norm_map]
    have h := hψ.grad_lipschitz.dist_le_mul (embeddingProjection J x) (embeddingProjection J y)
    simp only [dist_eq_norm, NNReal.coe_one, one_mul] at h
    exact h.trans (by simpa only [map_sub] using norm_embeddingProjection_le J (x - y))
  · simpa only [polyak.extendPotential, map_zero] using hψ.value_zero
  · rw [(hg 0).gradient]
    simp [hψ.gradient_zero]

/-- Article: genuine strongly convex extension to any larger Hilbert space.
Use: the extra orthogonal directions receive positive quadratic curvature. -/
def extendObjective (μ L : ℝ) (J : E →ₗᵢ[ℝ] F) (f : E → ℝ) : F → ℝ :=
  denormalizeFunction μ L (extendPotential J (normalizeFunction μ L f))

/-- Article: dimension extension preserves the genuine original class.
Proof: normalize, project the potential, and apply inverse normalization. -/
theorem CenteredSmoothStronglyConvex.extendObjective {μ L : ℝ} {f : E → ℝ}
    (hf : CenteredSmoothStronglyConvex μ L f) (J : E →ₗᵢ[ℝ] F) :
    CenteredSmoothStronglyConvex μ L (polyak.extendObjective μ L J f) :=
  (hf.normalize.extendPotential J).denormalize hf.mu_pos hf.mu_lt_L

/-- Article: extension preserves values on the embedded original space.
Proof: the projection is a left inverse and the normalization maps cancel. -/
theorem extendObjective_embed {μ L : ℝ} (hμL : μ < L)
    (J : E →ₗᵢ[ℝ] F) (f : E → ℝ) (x : E) :
    extendObjective μ L J f (J x) = f x := by
  dsimp [extendObjective, denormalizeFunction, extendPotential]
  rw [embeddingProjection_embed, J.norm_map]
  exact congrFun (denormalize_normalize hμL f) x

/-- Article: the actual extended gradient restricts to the original gradient.
Proof: the chain rule and the inverse normalization derivative dictionary. -/
theorem gradient_extendObjective_embed {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (J : E →ₗᵢ[ℝ] F) (x : E) :
    gradient (extendObjective μ L J f) (J x) = J (gradient f x) := by
  have hn : Differentiable ℝ (normalizeFunction μ L f) :=
    fun x => (hasGradientAt_normalize hf.differentiable x).differentiableAt
  have he : Differentiable ℝ (extendPotential J (normalizeFunction μ L f)) :=
    fun x => (hasGradientAt_extendPotential J hn x).differentiableAt
  unfold extendObjective
  rw [(hasGradientAt_denormalize (μ := μ) (L := L) he (J x)).gradient,
    (hasGradientAt_extendPotential J hn (J x)).gradient, embeddingProjection_embed]
  have hd := (hasGradientAt_denormalize (μ := μ) (L := L) hn x).gradient
  rw [denormalize_normalize hf.mu_lt_L f] at hd
  rw [hd, map_sub, map_smul, map_smul]

/-- Article: the canonical Hilbert inclusion into an orthogonal product.
Proof: its second coordinate is zero, so the squared L² norm is unchanged. -/
def hilbertInclusion : E →ₗᵢ[ℝ] WithLp 2 (E × F) where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap.comp (LinearMap.inl ℝ E F)
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp

/-- Article: Euclidean coordinate inclusion from d to d+k dimensions.
Use: a norm-preserving concrete map into the article's EuclideanSpace model. -/
def euclideanInclusion (d k : ℕ) :
    EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + k)) :=
  (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin d ⊕ Fin k => ℝ))).symm.toLinearIsometry).comp
      (hilbertInclusion (E := EuclideanSpace ℝ (Fin d)) (F := EuclideanSpace ℝ (Fin k)))

end polyak
