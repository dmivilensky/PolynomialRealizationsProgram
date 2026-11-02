import krylov.LinearAlgebra.FrobeniusSupport
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
Article: main_krylov, apG:mss, genuine spectral conditioning bounds.
Use: pass from the actual normalized entry errors to the printed dimension factor n.
Source: reuse the earlier actual Hilbert--Schmidt norm; rowwise finite Cauchy--Schwarz
compares its energy to the genuine Euclidean operator norm.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The genuine spectral matrix norm is bounded by the earlier actual Hilbert--Schmidt norm.
Use: the model-error estimate retains the printed factor n, not n².
Article: main_krylov, apG:mss, ‖X‖≤‖X‖_F.
Proof: rowwise Cauchy--Schwarz bounds every actual matrix-vector action;
sum the row energies and apply the actual operator-norm characterization. -/
theorem spectral_le_hsNorm (M : Matrix (Fin n) (Fin n) ℝ) : ‖M‖≤hsNorm M := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (hsNorm_nonneg M)
  intro v
  have hr (i : Fin n) : (M*ᵥ WithLp.ofLp v) i ^ 2 ≤
      (∑ j, M i j ^ 2)*‖v‖^2 := by
    simpa only [Matrix.mulVec, dotProduct, EuclideanSpace.real_norm_sq_eq] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) (WithLp.ofLp v)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hr i)
  simp only [← Finset.sum_mul] at hs
  have hv : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M v‖^2 ≤ hsSq M*‖v‖^2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, Matrix.ofLp_toEuclideanCLM, hsSq] using hs
  -- Both sides are nonnegative before passing from the squared energy to the norm.
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hsNorm_nonneg M) (norm_nonneg _))).mp
  rw [mul_pow, hsNorm_sq]
  exact hv

/-- Uniform actual entry bounds give the sharp dimension factor for the Frobenius norm comparison.
Use: actual normalized columns bound every model-error entry by the common operator deviation.
Article: main_krylov, apG:mss, ‖X‖_F≤n max_i‖Â_i−I‖.
Proof: square each actual entry bound, sum all n² entries and take nonnegative square roots. -/
theorem hsNorm_le_dimension (M : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0≤ε)
    (hM : ∀ i j, |M i j|≤ε) : hsNorm M≤n*ε := by
  -- Sum the n² true entry energies before comparing their nonnegative square roots.
  have hs : hsSq M≤(n : ℝ)^2*ε^2 := by
    unfold hsSq
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ε^2 := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => by
          have he := (sq_le_sq₀ (abs_nonneg _) hε).mpr (hM i j)
          simpa only [sq_abs] using he
      _ = _ := by simp; ring
  apply (sq_le_sq₀ (hsNorm_nonneg M) (mul_nonneg (Nat.cast_nonneg n) hε)).mp
  rw [hsNorm_sq, mul_pow]
  exact hs

end
end krylov.LinearAlgebra
