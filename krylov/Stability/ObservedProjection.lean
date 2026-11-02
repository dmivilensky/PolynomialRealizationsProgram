import krylov.Stability.UniformGram
import krylov.Methods.ProjectedRecording
import krylov.Methods.WindowCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Article: main_krylov, apB:lem:UAsteps, actual observed-span orthogonal projections.
Use: derive uniform real old-span conditioning, conjugacy and weighted
projection-change bounds from actual normalized observations, including empty spans.
Source: mathlib's true finite-dimensional orthogonal projection, the existing
real finite synthesis/coordinate identities and proved Neumann Gram bounds.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : ℕ}

/-- The genuine orthogonal projector onto the actual span of the observed columns.
Use: use the actual old physical subspace, with no presumed projection or inverse representation.
Article: main_krylov, apB:lem:UAsteps, P. -/
def observedProjection (s : Fin p → E) : E →L[ℝ] E :=
  (Submodule.span ℝ (Set.range s)).starProjection

/-- The real observed-span orthogonal projection preserves every actual observed-column pairing.
Use: identify its normal equations before expressing any inverse Gram.
Article: main_krylov, apB:lem:UAsteps.
Proof: each true observed column belongs to the actual span, so the real
projection residual is orthogonal to it. -/
theorem observedProjection_coordinates (s : Fin p → E) (g : E) :
    coordinates s (observedProjection s g)=coordinates s g := by
  ext i
  have ho := (Submodule.span ℝ (Set.range s)).starProjection_inner_eq_zero g (s i)
    (Submodule.subset_span (Set.mem_range_self i))
  rw [inner_sub_left] at ho
  simpa only [coordinates,observedProjection,real_inner_comm] using (sub_eq_zero.mp ho).symm

/-- The actual observed-span projector has the genuine finite inverse-Gram synthesis formula on its true nonsingular domain.
Use: normalized conditioning estimates apply to the real projector rather than an assumed matrix representation.
Article: main_krylov, apB:lem:UAsteps.
Proof: the actual projected vector is in the real span; the proved finite
normal-coordinate reconstruction and the actual preserved pairings give its formula. -/
theorem observedProjection_apply (s : Fin p → E) (hu : IsUnit (crossGram s s).det) (g : E) :
    observedProjection s g=combine s ((crossGram s s)⁻¹ *ᵥ coordinates s g) := by
  have he := combine_gram_coordinates s (observedProjection s g) hu
    ((Submodule.span ℝ (Set.range s)).starProjection_apply_mem g)
  rw [conjugacyCoefficients,observedProjection_coordinates] at he
  exact he.symm

/-- The genuine actual old-span projector has operator norm at most one, including the empty span.
Use: bound direction decompositions independently of any physical column length.
Article: main_krylov, apB:lem:UAsteps.
Proof: use the standard norm theorem for the true orthogonal projection. -/
theorem observedProjection_norm_le (s : Fin p → E) : ‖observedProjection s‖≤1 :=
  (Submodule.span ℝ (Set.range s)).starProjection_norm_le

omit [FiniteDimensional ℝ E] in
/-- A true column Gram matrix within one half of the identity has the uniform spectral bound four.
Use: rectangular physical synthesis is controlled without an inverse physical step length.
Article: main_krylov, apB:lem:UAsteps.
Proof: the true identity operator norm is at most one, also in dimension
zero; the actual Gram triangle inequality gives the claimed relaxed bound. -/
theorem gram_near_norm_le (s : Fin p → E) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ)) :
    ‖crossGram s s‖≤4 := by
  have h₁ : ‖(1 : Matrix (Fin p) (Fin p) ℝ)‖≤1 := by
    rw [Matrix.cstar_norm_def,map_one]
    exact ContinuousLinearMap.norm_id_le
  have ht := norm_add_le (crossGram s s-1) (1 : Matrix (Fin p) (Fin p) ℝ)
  rw [sub_add_cancel] at ht
  linarith

omit [FiniteDimensional ℝ E] in
/-- A true near-identity column Gram gives the uniform physical synthesis bound two.
Use: all rectangular observed-span coefficient actions use genuine Euclidean norms.
Article: main_krylov, apB:lem:UAsteps.
Proof: specialize the proved actual synthesis-energy bound to the true Gram norm bound four. -/
theorem gram_near_synthesis_bound (s : Fin p → E) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (c : Fin p → ℝ) : ‖combine s c‖≤2*‖WithLp.toLp 2 c‖ := by
  simpa only [show Real.sqrt (4 : ℝ)=2 by norm_num] using
    combine_norm_le s c (by norm_num : (0 : ℝ)≤4) (gram_near_norm_le s hG)

omit [FiniteDimensional ℝ E] in
/-- True near-identity Gram conditioning bounds the actual observed coordinate norm by twice the physical vector norm.
Use: actual analysis and synthesis are uniformly bounded without reference-step minima.
Article: main_krylov, apB:lem:UAsteps.
Proof: pair the actual coordinate synthesis with the original vector;
Cauchy--Schwarz and the proved true synthesis bound control its squared coordinate norm. -/
theorem gram_near_coordinates_bound (s : Fin p → E) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (g : E) : ‖projectedResidual s g‖≤2*‖g‖ := by
  have hS := gram_near_synthesis_bound s hG (coordinates s g)
  have hi := real_inner_le_norm (combine s (coordinates s g)) g
  rw [combine_inner_coordinates] at hi
  change inner ℝ (projectedResidual s g) (projectedResidual s g)≤‖combine s (coordinates s g)‖*‖g‖ at hi
  rw [real_inner_self_eq_norm_sq] at hi
  change ‖combine s (coordinates s g)‖≤2*‖projectedResidual s g‖ at hS
  have hp := mul_le_mul_of_nonneg_right hS (norm_nonneg g)
  nlinarith [norm_nonneg (projectedResidual s g),norm_nonneg g]

/-- The genuine actual old-span projection is at most four times its real observed-coordinate residual norm.
Use: conjugacy bounds on actual pairings become a true physical projected-direction bound.
Article: main_krylov, apB:lem:UAsteps.
Proof: the actual Gram inverse has norm at most two; combine its true
coordinate action with the physical synthesis bound two. -/
theorem observedProjection_residual_bound (s : Fin p → E) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (g : E) : ‖observedProjection s g‖≤4*‖projectedResidual s g‖ := by
  -- Apply the real Gram inverse to the actual observed residual before physical synthesis.
  obtain ⟨hu,hi,_⟩ := near_identity_inverse (crossGram s s) hG
  rw [observedProjection_apply s hu]
  have hS := gram_near_synthesis_bound s hG ((crossGram s s)⁻¹ *ᵥ coordinates s g)
  have he : WithLp.toLp 2 ((crossGram s s)⁻¹ *ᵥ coordinates s g)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (crossGram s s)⁻¹ (projectedResidual s g) := rfl
  rw [he] at hS
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) (crossGram s s)⁻¹).le_opNorm (projectedResidual s g)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  exact hS.trans (by nlinarith [mul_le_mul_of_nonneg_right hi (norm_nonneg (projectedResidual s g))])

/-- Actual observed-image conjugacy and true relative unit-pair errors bound the genuine old-span component of the real direction.
Use: gives the source bound ‖PD‖≤4sqrt(p)η‖D‖ with no physical-length denominator.
Article: main_krylov, apB:lem:UAsteps.
Proof: approximate real conjugacy bounds every true unit coordinate;
the genuine Euclidean coordinate bound and actual inverse-Gram projection
estimate give the result. -/
theorem observedProjection_conjugacy_bound (s y : Fin p → E)
    (hs : ∀ i, ‖s i‖=1) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ)) (d : E)
    {η : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-s i‖≤η) (ho : ∀ i, inner ℝ (y i) d=0) :
    ‖observedProjection s d‖≤4*Real.sqrt p*η*‖d‖ := by
  have hb : ‖projectedResidual s d‖≤Real.sqrt p*(η*‖d‖) := by
    apply coordinate_norm_le_sqrt_card _ (mul_nonneg hη (norm_nonneg d))
    intro i
    have he := approximate_conjugacy_bound (s i) (y i) d (ContinuousLinearMap.id ℝ E)
      (hs i) (ε := 0) (by simp) (hy i) (ho i)
    simpa only [coordinates,ContinuousLinearMap.id_apply,zero_add] using he
  exact (observedProjection_residual_bound s hG d).trans
    ((mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ)≤4)).trans_eq (by ring))

/-- The genuine sum of rank-one operators of the supplied actual columns.
Use: separate the actual inverse-Gram error from true normalized column changes.
Article: main_krylov, eq:weighted-flags. -/
def observedFrameSum (s : Fin p → E) : E →L[ℝ] E :=
  ∑ i, InnerProductSpace.rankOne ℝ (s i) (s i)

omit [FiniteDimensional ℝ E] in
/-- The real rank-one frame sum acts by the actual observed-coordinate synthesis.
Use: compare actual span projections with the genuine unit-column outer-product sum.
Article: main_krylov, eq:weighted-flags.
Proof: expand the true finite rank-one actions and their actual observed pairings. -/
theorem observedFrameSum_apply (s : Fin p → E) (g : E) :
    observedFrameSum s g=combine s (coordinates s g) := by
  simp only [observedFrameSum,_root_.sum_apply,InnerProductSpace.rankOne_apply,combine,coordinates]

/-- A true identity column Gram makes the genuine observed-span projection exactly its actual rank-one frame sum.
Use: the real CG orthonormal old-span projector has precisely the source outer-product representation.
Article: main_krylov, eq:weighted-flags.
Proof: the actual inverse-Gram projection formula reduces to identity coefficients. -/
theorem observedProjection_eq_frameSum (s : Fin p → E) (hG : crossGram s s=1) :
    observedProjection s=observedFrameSum s := by
  have hu : IsUnit (crossGram s s).det := by rw [hG]; simp
  ext g
  rw [observedProjection_apply s hu,hG,inv_one,Matrix.one_mulVec,observedFrameSum_apply]

/-- The actual old-span projector differs from its real unit-column frame sum by at most eight times the genuine spectral Gram error.
Use: quantify the exact source inverse-Gram correction with dimension-free normalized constants.
Article: main_krylov, eq:weighted-flags.
Proof: subtract the true frame synthesis from the proved actual projector
formula. The remaining actual inverse-Gram deviation has its genuine Neumann
bound, while the real analysis and synthesis bounds each contribute two. -/
theorem observedProjection_gram_error (s : Fin p → E) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ)) :
    ‖observedProjection s-observedFrameSum s‖≤8*‖crossGram s s-1‖ := by
  -- Both operator factors use true spectral norms; no entrywise matrix norm appears.
  obtain ⟨hu,_,hi⟩ := near_identity_inverse (crossGram s s) hG
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro g
  change ‖observedProjection s g-observedFrameSum s g‖≤_
  rw [observedProjection_apply s hu,observedFrameSum_apply]
  have he : combine s ((crossGram s s)⁻¹ *ᵥ coordinates s g)-combine s (coordinates s g)=
      combine s (((crossGram s s)⁻¹-1) *ᵥ coordinates s g) := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec]
    simp only [combine,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
  rw [he]
  have hS := gram_near_synthesis_bound s hG (((crossGram s s)⁻¹-1) *ᵥ coordinates s g)
  have hc : WithLp.toLp 2 (((crossGram s s)⁻¹-1) *ᵥ coordinates s g)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) ((crossGram s s)⁻¹-1) (projectedResidual s g) := rfl
  rw [hc] at hS
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) ((crossGram s s)⁻¹-1)).le_opNorm (projectedResidual s g)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  have hb := ho.trans (mul_le_mul hi (gram_near_coordinates_bound s hG g)
    (norm_nonneg _) (by positivity))
  exact hS.trans (by nlinarith)

/-- The genuine actual old-span projection has the printed weighted Gram-plus-rank-one change bound.
Use: keep each genuine later-reference-error weight paired with its actual old-column change, avoiding a smallest reference energy.
Article: main_krylov, eq:weighted-flags and apB:lem:UAsteps.
Proof: insert the actual column frame sum between the two genuine
operators; the proved inverse-Gram correction controls its first difference,
and the true finite sum of weighted rank-one changes controls the second. -/
theorem observedProjection_weighted_change (s q : Fin p → E)
    (hG : ‖crossGram s s-1‖≤(1/2 : ℝ)) {r β : ℝ} (hr : 0≤r)
    (hcol : ∀ i, r*‖InnerProductSpace.rankOne ℝ (s i) (s i)-InnerProductSpace.rankOne ℝ (q i) (q i)‖≤β) :
    r*‖observedProjection s-observedFrameSum q‖≤8*r*‖crossGram s s-1‖+(p : ℝ)*β := by
  -- The true frame sum is inserted before taking norms, keeping every actual old-column weight.
  have he : observedProjection s-observedFrameSum q=
      (observedProjection s-observedFrameSum s)+(observedFrameSum s-observedFrameSum q) := by abel
  rw [he]
  have ht := norm_add_le (observedProjection s-observedFrameSum s) (observedFrameSum s-observedFrameSum q)
  have hs : r*‖observedFrameSum s-observedFrameSum q‖≤(p : ℝ)*β := by
    rw [observedFrameSum,observedFrameSum,← Finset.sum_sub_distrib]
    calc
      _ ≤ r*∑ i : Fin p, ‖InnerProductSpace.rankOne ℝ (s i) (s i)-InnerProductSpace.rankOne ℝ (q i) (q i)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
      _ = ∑ i : Fin p, r*‖InnerProductSpace.rankOne ℝ (s i) (s i)-InnerProductSpace.rankOne ℝ (q i) (q i)‖ :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin p, β := Finset.sum_le_sum fun i _ => hcol i
      _ = _ := by simp
  have hp := mul_le_mul_of_nonneg_left (observedProjection_gram_error s hG) hr
  exact (mul_le_mul_of_nonneg_left ht hr).trans (by nlinarith)

end
end krylov.Stability
