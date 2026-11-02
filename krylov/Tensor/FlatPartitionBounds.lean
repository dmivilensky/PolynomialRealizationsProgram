import krylov.Tensor.FlagResponse

/-!
Article: main_krylov, apG:flat, genuine orthogonal partition estimates.
Use: control the actual restricted output vector on disjoint dyadic blocks
by Bessel and Cauchy--Schwarz before summing the true tensor decomposition.
Source: standard Hilbert-space orthogonality and finite Cauchy--Schwarz.
-/

namespace krylov.Tensor
noncomputable section
open Finset
open scoped BigOperators InnerProductSpace
variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] [DecidableEq ι] in
/-- The squared norm of an actual orthogonal coordinate restriction is exactly its coordinate energy.
Article: main_krylov, apG:flat, actual restricted vector norms. -/
theorem norm_flagComponent_sq (e : ι → E) (he : Orthonormal ℝ e) (I : Finset ι) (u : E) :
    ‖flagComponent e I u‖ ^ 2 = ∑ i ∈ I, ‖inner ℝ (e i) u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold flagComponent
  rw [he.inner_sum]
  simp only [conj_trivial, Real.norm_eq_abs, sq_abs, ← pow_two]

omit [Fintype ι] in
/-- Genuine disjoint orthogonal restrictions together carry at most the original output energy.
Article: main_krylov, apG:flat, the dyadic layer Cauchy--Schwarz input.
Proof: merge the actual disjoint finite supports and apply Bessel to their union. -/
theorem sum_norm_flagComponent_sq_le (e : ι → E) (he : Orthonormal ℝ e)
    (I : κ → Finset ι) (hI : Pairwise (fun a b => Disjoint (I a) (I b))) (u : E) :
    ∑ j : κ, ‖flagComponent e (I j) u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  simp_rw [norm_flagComponent_sq e he]
  rw [← Finset.sum_biUnion (fun a _ b _ hab => hI hab)]
  exact he.sum_inner_products_le u

omit [Fintype ι] in
/-- The sum of actual disjoint restricted vector norms is bounded by the square root of the number of blocks.
Article: main_krylov, apG:flat, genuine layer estimate.
Proof: finite Cauchy--Schwarz and the true orthogonal energy bound. -/
theorem sum_norm_flagComponent_le (e : ι → E) (he : Orthonormal ℝ e)
    (I : κ → Finset ι) (hI : Pairwise (fun a b => Disjoint (I a) (I b))) (u : E) :
    ∑ j : κ, ‖flagComponent e (I j) u‖ ≤ Real.sqrt (Fintype.card κ) * ‖u‖ := by
  have hs := sum_norm_flagComponent_sq_le e he I hI u
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := (univ : Finset κ))
    (fun _ : κ => (1 : ℝ)) (fun j => ‖flagComponent e (I j) u‖)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at hc
  have hsum : 0 ≤ ∑ j : κ, ‖flagComponent e (I j) u‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have hcard : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  have hb := mul_le_mul_of_nonneg_left hs hcard
  have hn := Real.sqrt_nonneg (Fintype.card κ : ℝ)
  have hsq : (∑ j : κ, ‖flagComponent e (I j) u‖) ^ 2 ≤ (Real.sqrt (Fintype.card κ) * ‖u‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcard]
    exact hc.trans hb
  exact (sq_le_sq₀ hsum (mul_nonneg hn (norm_nonneg u))).mp hsq

omit [Fintype ι] [DecidableEq ι] in
/-- The actual sum of orthonormal coordinate vectors has norm equal to the square root of its support size.
Article: main_krylov, apG:flat, true dyadic indicator-vector norms. -/
theorem norm_orthonormal_sum (e : ι → E) (he : Orthonormal ℝ e) (I : Finset ι) :
    ‖∑ i ∈ I, e i‖ = Real.sqrt (I.card : ℝ) := by
  have hs : ‖∑ i ∈ I, e i‖ ^ 2 = (I.card : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    have h := he.inner_sum (s := I) (l₁ := fun _ => (1 : ℝ)) (l₂ := fun _ => (1 : ℝ))
    simpa only [one_smul, conj_trivial, one_mul, sum_const, nsmul_eq_mul, mul_one] using h
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hs.trans (Real.sq_sqrt (Nat.cast_nonneg _)).symm)

end
end krylov.Tensor
