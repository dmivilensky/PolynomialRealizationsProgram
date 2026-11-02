import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Article: main_krylov, Appendix A, apA:galerkin(c), orthogonal compression.
Use: retain the sharp cross-block loss that is absent from a plain norm-product bound.
Source: Bessel's inequality, orthogonal projection and symmetry of the actual operator.
-/

namespace krylov.LinearAlgebra
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Projection onto a subspace and a unit vector in its orthogonal complement
collect at most the full squared norm.
Use: the exact missing cross-block term in the compression estimate.
Article: main_krylov, apA:galerkin(c), quadratic compression argument.
Source: mathlib orthogonal projection decomposition and Cauchy--Schwarz.
Proof: apply Cauchy--Schwarz to the complementary projection and use Pythagoras. -/
theorem projection_bessel (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (h : E) (hh : h ∈ Kᗮ) (hn : ‖h‖ = 1) (w : E) :
    ‖K.starProjection w‖^2 + (inner ℝ h w)^2 ≤ ‖w‖^2 := by
  -- Separate the old-subspace energy from its orthogonal complement.
  have hfix : Kᗮ.starProjection h = h := Kᗮ.starProjection_eq_self_iff.mpr hh
  have he : inner ℝ h w = inner ℝ h (Kᗮ.starProjection w) := by
    simpa only [hfix] using Kᗮ.inner_starProjection_left_eq_right h w
  have hc : |inner ℝ h (Kᗮ.starProjection w)| ≤ ‖Kᗮ.starProjection w‖ := by
    simpa only [Real.norm_eq_abs, hn, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) h (Kᗮ.starProjection w)
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hc
  rw [sq_abs, ← he] at hs
  have hp := K.norm_sq_eq_add_norm_sq_starProjection w
  linarith

/-- The full quadratic compression bound with its exact projection on the right.
Use: equivalent quadratic-form statement of Y²+xx* ≤ ω²P.
Article: main_krylov, apA:galerkin(c), first displayed inequality.
Proof: apply the two-component Bessel bound to T(Pv), move T and P across
the inner product using symmetry, and use the actual operator norm. -/
theorem compression_quadratic (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) {ω : ℝ} (hω : ‖T‖ ≤ ω)
    (h : E) (hh : h ∈ Kᗮ) (hn : ‖h‖ = 1) (v : E) :
    ‖K.starProjection (T (K.starProjection v))‖^2 +
      (inner ℝ (K.starProjection (T h)) v)^2 ≤ ω^2 * ‖K.starProjection v‖^2 := by
  -- The cross pairing is unchanged when T and the orthogonal projector are transposed.
  have he : inner ℝ (K.starProjection (T h)) v = inner ℝ h (T (K.starProjection v)) := by
    rw [K.inner_starProjection_left_eq_right]
    exact hT.isSymmetric h (K.starProjection v)
  have hb := projection_bessel K h hh hn (T (K.starProjection v))
  have ho : 0 ≤ ω := (norm_nonneg T).trans hω
  have ht : ‖T (K.starProjection v)‖ ≤ ω * ‖K.starProjection v‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ho (norm_nonneg _))).mpr ht
  rw [he]
  nlinarith

/-- The compression-action bound valid for every ambient vector, not only the old subspace.
Use: the sharp inequality used when aggregating second-order residuals.
Article: main_krylov, apA:galerkin(c), ‖YX‖² ≤ ω²‖X‖²−⟨x,X⟩².
Proof: the stronger quadratic inequality and contractivity of the old projection suffice. -/
theorem compression_action (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) {ω : ℝ} (hω : ‖T‖ ≤ ω)
    (h : E) (hh : h ∈ Kᗮ) (hn : ‖h‖ = 1) (v : E) :
    ‖K.starProjection (T (K.starProjection v))‖^2 ≤
      ω^2 * ‖v‖^2 - (inner ℝ (K.starProjection (T h)) v)^2 := by
  have hb := compression_quadratic K T hT hω h hh hn v
  have hp := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (K.norm_starProjection_apply_le v)
  nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg ω)]

end krylov.LinearAlgebra
