import krylov.LinearAlgebra.Compression
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Module.Normalize

/-!
Article: main_krylov, lem:aggregate, summed compression bounds.
Use: aggregate correlated cross and old-subspace actions without losing the
square-root tradeoff by separate triangle inequalities.
Source: Minkowski's inequality in the Euclidean plane and the proved orthogonal compression bound.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Finset
open scoped BigOperators InnerProductSpace
variable {ι : Type*}

/-- A finite sum of points in discs of radii ω_l lies in the disc of summed radius.
Use: the sharp joint aggregation step for both spectral and Frobenius compression budgets.
Article: main_krylov, lem:aggregate, the concavity/Minkowski step.
Source: the Euclidean triangle inequality, including zero and empty budgets.
Proof: form the actual planar vectors (a_l,b_l), bound each norm and apply the
finite-sum triangle inequality before squaring the nonnegative sides. -/
theorem sum_disc_bound (I : Finset ι) (a b ω : ι → ℝ)
    (hω : ∀ i ∈ I, 0 ≤ ω i) (hab : ∀ i ∈ I, (a i)^2 + (b i)^2 ≤ (ω i)^2) :
    (∑ i ∈ I, a i)^2 + (∑ i ∈ I, b i)^2 ≤ (∑ i ∈ I, ω i)^2 := by
  -- Keep both correlated scalar components in one actual Euclidean vector.
  let z : ι → EuclideanSpace ℝ (Fin 2) := fun i => WithLp.toLp 2 ![a i, b i]
  have hz : ∀ i, ‖z i‖^2 = (a i)^2 + (b i)^2 := by
    intro i
    simp [z, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hsum : ‖∑ i ∈ I, z i‖^2 = (∑ i ∈ I, a i)^2 + (∑ i ∈ I, b i)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, z]
  have hn : ‖∑ i ∈ I, z i‖ ≤ ∑ i ∈ I, ω i := by
    apply (norm_sum_le I z).trans
    apply sum_le_sum
    intro i hi
    exact (sq_le_sq₀ (norm_nonneg _) (hω i hi)).mp (by rw [hz]; exact hab i hi)
  rw [← hsum]
  exact (sq_le_sq₀ (norm_nonneg _) (sum_nonneg hω)).mpr hn

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The sum of actual old-subspace compressions retains the sharp cross-action loss.
Use: proves the first two spectral aggregation bounds without normalizing or dividing by X.
Article: main_krylov, lem:aggregate, ‖X‖≤W and ‖YX‖≤‖X‖√(W²−‖X‖²).
Proof: apply each actual compression to X, then sum the correlated pairs
(⟨x_l,X⟩,‖Y_lX‖) in the Euclidean plane before taking square roots. -/
theorem aggregated_compression_action (I : Finset ι) (K : ι → Submodule ℝ E)
    [∀ i, (K i).HasOrthogonalProjection] (T : ι → E →L[ℝ] E)
    (hT : ∀ i ∈ I, IsSelfAdjoint (T i)) (ω : ι → ℝ)
    (hω : ∀ i ∈ I, ‖T i‖ ≤ ω i) (h : E) (hh : ∀ i ∈ I, h ∈ (K i)ᗮ) (hn : ‖h‖ = 1) :
    let X := ∑ i ∈ I, (K i).starProjection (T i h)
    let W := ∑ i ∈ I, ω i
    ‖X‖ ≤ W ∧
      ‖∑ i ∈ I, (K i).starProjection (T i ((K i).starProjection X))‖ ≤
        ‖X‖ * Real.sqrt (W^2 - ‖X‖^2) := by
  dsimp only
  let X := ∑ i ∈ I, (K i).starProjection (T i h)
  let W := ∑ i ∈ I, ω i
  have hw : ∀ i ∈ I, 0 ≤ ω i := fun i hi => (norm_nonneg _).trans (hω i hi)
  have hW : 0 ≤ W := sum_nonneg hw
  have hX : ‖X‖ ≤ W := by
    apply (norm_sum_le I _).trans
    apply sum_le_sum
    intro i hi
    exact ((K i).norm_starProjection_apply_le _).trans
      (by simpa only [hn, mul_one] using
        ((T i).le_opNorm h).trans (mul_le_mul_of_nonneg_right (hω i hi) (norm_nonneg h)))
  refine ⟨hX, ?_⟩
  -- The pairing sum is exactly ‖X‖², so no nonzero-X case or division is required.
  have ha : ∑ i ∈ I, inner ℝ ((K i).starProjection (T i h)) X = ‖X‖^2 := by
    rw [← sum_inner]
    exact real_inner_self_eq_norm_sq X
  have hd := sum_disc_bound I
    (fun i => inner ℝ ((K i).starProjection (T i h)) X)
    (fun i => ‖(K i).starProjection (T i ((K i).starProjection X))‖)
    (fun i => ω i * ‖X‖) (fun i hi => mul_nonneg (hw i hi) (norm_nonneg _))
    (fun i hi => by
      have hc := compression_action (K i) (T i) (hT i hi) (hω i hi) h (hh i hi) hn X
      nlinarith)
  rw [ha, ← sum_mul] at hd
  have hnorm := norm_sum_le I (fun i => (K i).starProjection (T i ((K i).starProjection X)))
  have hs := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _)).mpr hnorm
  have hr : 0 ≤ W^2 - ‖X‖^2 := sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hW).mpr hX)
  have hroot := Real.sq_sqrt hr
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  nlinarith

omit [CompleteSpace E] in
/-- The summed hidden diagonal is bounded by the same sharp cross-action tradeoff.
Use: completes all three spectral inequalities for the actual compressed operators.
Article: main_krylov, lem:aggregate, |γ|≤√(W²−‖X‖²).
Proof: test the cross actions against the normalized actual sum X (zero when X=0),
apply the projection Bessel bound, and sum the resulting planar discs. -/
theorem aggregated_hidden_diagonal (I : Finset ι) (K : ι → Submodule ℝ E)
    [∀ i, (K i).HasOrthogonalProjection] (T : ι → E →L[ℝ] E)
    (ω : ι → ℝ) (hω : ∀ i ∈ I, ‖T i‖ ≤ ω i)
    (h : E) (hh : ∀ i ∈ I, h ∈ (K i)ᗮ) (hn : ‖h‖ = 1) :
    |∑ i ∈ I, inner ℝ h (T i h)| ≤ Real.sqrt ((∑ i ∈ I, ω i)^2 -
      ‖∑ i ∈ I, (K i).starProjection (T i h)‖^2) := by
  let X := ∑ i ∈ I, (K i).starProjection (T i h)
  let v := NormedSpace.normalize X
  have hv : ‖v‖ ≤ 1 := by
    by_cases hx : X = 0
    · simp [v, hx]
    · exact (NormedSpace.norm_normalize hx).le
  have hp : inner ℝ X v = ‖X‖ := by
    by_cases hx : X = 0
    · simp [hx]
    · change inner ℝ X (‖X‖⁻¹ • X) = ‖X‖
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq,
        pow_two, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_mul]
  -- Each planar cross/diagonal pair lies in its actual operator-budget disc.
  have hd := sum_disc_bound I (fun i => inner ℝ ((K i).starProjection (T i h)) v)
    (fun i => inner ℝ h (T i h)) ω
    (fun i hi => (norm_nonneg _).trans (hω i hi)) (fun i hi => by
      have hb := projection_bessel (K i) h (hh i hi) hn (T i h)
      have hc : |inner ℝ ((K i).starProjection (T i h)) v| ≤
          ‖(K i).starProjection (T i h)‖ := by
        have hc := norm_inner_le_norm (𝕜 := ℝ) ((K i).starProjection (T i h)) v
        rw [Real.norm_eq_abs] at hc
        exact hc.trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg
            ((K i).starProjection (T i h))))
      have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hc
      rw [sq_abs] at hs
      have ht : ‖T i h‖ ≤ ω i := by
        simpa only [hn, mul_one] using ((T i).le_opNorm h).trans
          (mul_le_mul_of_nonneg_right (hω i hi) (norm_nonneg h))
      have hts := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hω i hi))).mpr ht
      linarith)
  rw [← sum_inner, hp] at hd
  have hr : 0 ≤ (∑ i ∈ I, ω i)^2 - ‖X‖^2 := by nlinarith [sq_nonneg (∑ i ∈ I, inner ℝ h (T i h))]
  have hs := Real.sq_sqrt hr
  have ha := sq_abs (∑ i ∈ I, inner ℝ h (T i h))
  have hz := Real.sqrt_nonneg ((∑ i ∈ I, ω i)^2 - ‖X‖^2)
  change |∑ i ∈ I, inner ℝ h (T i h)| ≤ _
  nlinarith [abs_nonneg (∑ i ∈ I, inner ℝ h (T i h))]

end Hilbert

end
end krylov.LinearAlgebra
