import chebyshev1.Spectral.Resolvent
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Schur majorization, both as a convex combination of permutations and in convex order. -/
namespace chebyshev1.SpectralBasis
noncomputable section
open Matrix Set
open scoped BigOperators
variable {d : Type*} [Fintype d] [DecidableEq d] {H : Matrix d d ℝ}

theorem weight_doublyStochastic (B : SpectralBasis H) :
    (fun i j => B.weight i j) ∈ doublyStochastic ℝ d := by
  exact mem_doublyStochastic_iff_sum.mpr
    ⟨B.weight_nonneg, B.weight_sum, B.weight_column_sum⟩

/-- Every spectral diagonal is a convex combination of permutations of its eigenvalues. -/
theorem diagonal_convex_permutations (B : SpectralBasis H) (v : d → ℝ) :
    ∃ w : Equiv.Perm d → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      ∀ i, (∑ j, B.weight i j * v j) = ∑ σ, w σ * v (σ i) := by
  obtain ⟨w, hw, hsum, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (B.weight_doublyStochastic)
  refine ⟨w, hw, hsum, ?_⟩
  intro i
  calc
    _ = ((fun i j => B.weight i j) *ᵥ v) i := rfl
    _ = ((∑ σ, w σ • σ.permMatrix ℝ) *ᵥ v) i := by rw [he]
    _ = _ := by simp [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.permMatrix_mulVec]

/-- The convex-order form of Schur majorization, for every convex real function. -/
theorem diagonal_convex_sum_le (B : SpectralBasis H) (v : d → ℝ)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) :
    (∑ i, f (∑ j, B.weight i j * v j)) ≤ ∑ j, f (v j) := by
  have hi (i : d) : f (∑ j, B.weight i j * v j) ≤ ∑ j, B.weight i j * f (v j) := by
    simpa only [smul_eq_mul] using hf.map_sum_le
      (t := Finset.univ) (w := B.weight i) (p := v)
      (fun j _ => B.weight_nonneg i j) (B.weight_sum i) (by simp)
  calc
    _ ≤ ∑ i, ∑ j, B.weight i j * f (v j) := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, B.weight_column_sum, one_mul]

/-- In particular the resolvent diagonal is majorized by the reciprocal spectral gaps. -/
theorem resolvent_convex_sum_le (B : SpectralBasis H) (x : ℝ)
    (hx : ∀ j, x - B.eigenvalues j ≠ 0) (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) :
    (∑ i, f ((Matrix.scalar d x - H)⁻¹ i i)) ≤
      ∑ j, f (1 / (x - B.eigenvalues j)) := by
  simp_rw [B.resolvent_diagonal_sum x hx, div_eq_mul_inv, one_mul]
  exact B.diagonal_convex_sum_le _ f hf

end
end chebyshev1.SpectralBasis
