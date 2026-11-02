import krylov.Strings.SpectralSpace
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
Article: main_krylov, thm:value, bounded Neumann form resolvent.
Use: compress the genuine orthogonal energy-graph projection to the mass
coordinate. Its positivity, selfadjointness, two contraction bounds and
fixed/kernel spaces follow from Hilbert geometry, without an assumed
resolvent or spectral identity. Actual string energy constraints specialize
this construction separately.
Source: orthogonal projection and the Hilbert L² product in mathlib.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The mass coordinate embeds isometrically in the energy product. -/
def firstInclusion : E →ₗᵢ[ℂ] WithLp 2 (E × F) where
  toFun x := WithLp.toLp 2 (x, 0)
  map_add' x y := by
    change WithLp.toLp 2 (x + y, (0 : F)) = WithLp.toLp 2 (x + y, (0 : F) + 0)
    rw [add_zero]
  map_smul' r x := by
    change WithLp.toLp 2 (r • x, (0 : F)) = WithLp.toLp 2 (r • x, r • (0 : F))
    rw [smul_zero]
  norm_map' x := WithLp.norm_toLp_fst 2 E F x

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem firstInclusion_apply (x : E) :
    firstInclusion (F := F) x = WithLp.toLp 2 (x, 0) := rfl

/-- The bounded solution of the energy-space variational problem. -/
def compressedSolution (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection] :
    E →L[ℂ] WithLp 2 (E × F) := K.starProjection ∘L firstInclusion.toContinuousLinearMap

/-- Compression of an actual closed energy-subspace projection to mass. -/
def compressedProjection (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection] : E →L[ℂ] E :=
  WithLp.fstL 2 ℂ E F ∘L compressedSolution K

omit [CompleteSpace E] [CompleteSpace F] in
/-- The projected solution obeys the actual variational identity. -/
theorem compressedSolution_variational (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection]
    (x : E) {w : WithLp 2 (E × F)} (hw : w ∈ K) :
    inner ℂ (compressedSolution K x) w = inner ℂ (firstInclusion x) w := by
  have h := K.starProjection_inner_eq_zero (firstInclusion x) w hw
  rw [inner_sub_left] at h
  exact (sub_eq_zero.1 h).symm

omit [CompleteSpace F] in
theorem compressedProjection_selfAdjoint (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection] :
    IsSelfAdjoint (compressedProjection K) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
  intro x y
  change inner ℂ (K.starProjection (firstInclusion x)).fst y =
    inner ℂ x (K.starProjection (firstInclusion y)).fst
  have h := K.inner_starProjection_left_eq_right (firstInclusion x) (firstInclusion y)
  simpa only [firstInclusion_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, WithLp.ofLp_fst, inner_zero_left, inner_zero_right, add_zero] using h

omit [CompleteSpace E] [CompleteSpace F] in
theorem compressedProjection_norm_le (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection] :
    ‖compressedProjection K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(K.starProjection (firstInclusion x)).fst‖ ≤ 1 * ‖x‖
  calc
    _ ≤ ‖K.starProjection (firstInclusion x)‖ := WithLp.norm_fst_le E _
    _ ≤ ‖firstInclusion (F := F) x‖ := K.norm_starProjection_apply_le _
    _ = _ := by rw [firstInclusion.norm_map, one_mul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The complementary compressed projection is exactly the complementary
contraction. This avoids a separate positive-operator spectrum argument. -/
theorem compressedProjection_complement (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection] :
    1 - compressedProjection K = compressedProjection Kᗮ := by
  ext x
  have h := congrArg (fun w : WithLp 2 (E × F) => w.fst)
    (K.starProjection_add_starProjection_orthogonal (firstInclusion x))
  change x - (K.starProjection (firstInclusion x)).fst = (Kᗮ.starProjection (firstInclusion x)).fst
  simp only [WithLp.add_fst] at h
  change (K.starProjection (firstInclusion x)).fst + (Kᗮ.starProjection (firstInclusion x)).fst = x at h
  exact eq_sub_of_add_eq' h |>.symm

omit [CompleteSpace E] [CompleteSpace F] in
theorem compressedProjection_complement_norm_le (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection] :
    ‖1 - compressedProjection K‖ ≤ 1 := by
  rw [compressedProjection_complement]
  exact compressedProjection_norm_le _

omit [CompleteSpace E] [CompleteSpace F] in
/-- Kernel vectors are exactly those whose pure mass lift is orthogonal to
the actual energy graph. -/
theorem compressedProjection_eq_zero_iff (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection]
    (x : E) : compressedProjection K x = 0 ↔ firstInclusion (F := F) x ∈ Kᗮ := by
  constructor
  · intro hx
    have hnorm := K.re_inner_starProjection_eq_normSq (firstInclusion x)
    have hinner : RCLike.re (inner ℂ (K.starProjection (firstInclusion x)) (firstInclusion x)) = 0 := by
      rw [WithLp.prod_inner_apply]
      change RCLike.re (inner ℂ (K.starProjection (firstInclusion x)).fst x + inner ℂ
        (K.starProjection (firstInclusion x)).snd 0) = 0
      change (K.starProjection (firstInclusion x)).fst = 0 at hx
      rw [hx, inner_zero_left, inner_zero_right, add_zero, map_zero]
    rw [hinner] at hnorm
    have hzero : K.starProjection (firstInclusion x) = 0 := by
      apply norm_eq_zero.1
      change ‖K.orthogonalProjectionOnto (firstInclusion x)‖ = 0
      exact sq_eq_zero_iff.1 hnorm.symm
    change firstInclusion x ∈ Kᗮ
    rw [← K.ker_starProjection]
    exact hzero
  · intro hx
    have hzero : K.starProjection (firstInclusion x) = 0 := by
      rw [← K.ker_starProjection] at hx
      exact hx
    change (K.starProjection (firstInclusion x)).fst = 0
    rw [hzero]
    rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Fixed vectors are exactly the mass vectors whose zero-gradient lift
lies in the true energy graph. -/
theorem compressedProjection_fixed_iff (K : Submodule ℂ (WithLp 2 (E × F))) [K.HasOrthogonalProjection]
    (x : E) : compressedProjection K x = x ↔ firstInclusion (F := F) x ∈ K := by
  have hzero := compressedProjection_eq_zero_iff Kᗮ x
  rw [K.orthogonal_orthogonal] at hzero
  rw [← compressedProjection_complement] at hzero
  change x - compressedProjection K x = 0 ↔ _ at hzero
  constructor
  · intro h
    apply hzero.1
    rw [h, sub_self]
  · intro h
    exact (sub_eq_zero.1 (hzero.2 h)).symm

end
end krylov.Strings.Spectral
