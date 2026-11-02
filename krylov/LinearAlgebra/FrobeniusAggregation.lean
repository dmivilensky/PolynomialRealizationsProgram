import krylov.LinearAlgebra.Aggregation
import krylov.LinearAlgebra.HilbertSchmidtCompression

/-!
Article: main_krylov, lem:aggregate, Frobenius aggregation bounds.
Use: aggregate the actual twice-counted symmetric cross actions with the same
proved planar Minkowski argument, retaining the improved square-root loss.
Source: the actual Hilbert--Schmidt compression inequalities and sum_disc_bound.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Finset chebyshev1
open scoped Matrix InnerProductSpace BigOperators
variable {ι : Type*} {n : ℕ}

/-- Both improved Frobenius aggregation inequalities for actual symmetric matrix increments.
Use: the full upper-bound part of the Frobenius aggregated-compression lemma,
including zero budgets and an actual zero cross-action sum.
Article: main_krylov, lem:aggregate, eq:aggregate-F.
Proof: the actual √2 cross costs give the first bound; sum the correlated
(√2⟨x_l,X⟩,‖Y_lX‖) discs for the exact improved action loss. -/
theorem frobenius_aggregated_compression (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (E : ι → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ i ∈ I, (E i).IsSymm)
    (ω : ι → ℝ) (hω : ∀ i ∈ I, hsNorm (E i) ≤ ω i)
    (h : EuclideanSpace ℝ (Fin n)) (hh : ∀ i ∈ I, h ∈ (K i)ᗮ) (hn : ‖h‖ = 1) :
    let T := fun i => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E i)
    let X := ∑ i ∈ I, (K i).starProjection (T i h)
    let W := ∑ i ∈ I, ω i
    Real.sqrt 2 * ‖X‖ ≤ W ∧
      ‖∑ i ∈ I, (K i).starProjection (T i ((K i).starProjection X))‖ ≤
        ‖X‖ * Real.sqrt (W^2 - 2 * ‖X‖^2) := by
  dsimp only
  let T := fun i => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E i)
  let X := ∑ i ∈ I, (K i).starProjection (T i h)
  let W := ∑ i ∈ I, ω i
  have hw : ∀ i ∈ I, 0 ≤ ω i := fun i hi => (hsNorm_nonneg _).trans (hω i hi)
  have hW : 0 ≤ W := sum_nonneg hw
  have hx : ∀ i ∈ I, Real.sqrt 2 * ‖(K i).starProjection (T i h)‖ ≤ ω i :=
    fun i hi => hs_cross_norm (E i) (hE i hi) (K i) h (hh i hi) hn (hω i hi)
  have hX : Real.sqrt 2 * ‖X‖ ≤ W := by
    have ht := mul_le_mul_of_nonneg_left (norm_sum_le I (fun i => (K i).starProjection (T i h)))
      (Real.sqrt_nonneg 2)
    apply ht.trans
    rw [Finset.mul_sum]
    exact sum_le_sum hx
  refine ⟨hX, ?_⟩
  -- Correlated Frobenius disks retain the full twice-counted cross-action energy.
  have ha : ∑ i ∈ I, Real.sqrt 2 * inner ℝ ((K i).starProjection (T i h)) X =
      Real.sqrt 2 * ‖X‖^2 := by rw [← Finset.mul_sum, ← sum_inner, real_inner_self_eq_norm_sq]
  have hd := sum_disc_bound I
    (fun i => Real.sqrt 2 * inner ℝ ((K i).starProjection (T i h)) X)
    (fun i => ‖(K i).starProjection (T i ((K i).starProjection X))‖)
    (fun i => ω i * ‖X‖) (fun i hi => mul_nonneg (hw i hi) (norm_nonneg _))
    (fun i hi => by
      have hc := hs_compression_action (E i) (hE i hi) (K i) h (hh i hi) hn (hω i hi) X
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
      linarith)
  rw [ha, ← sum_mul, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hd
  have hb := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg X)) hW).mpr hX
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hb
  have hr : 0 ≤ W^2 - 2 * ‖X‖^2 := sub_nonneg.mpr hb
  have hnY := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _)).mpr
    (norm_sum_le I (fun i => (K i).starProjection (T i ((K i).starProjection X))))
  have hs := Real.sq_sqrt hr
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  nlinarith

end
end krylov.LinearAlgebra
