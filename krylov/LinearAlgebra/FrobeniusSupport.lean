import chebyshev1.Spectral.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Article: main_krylov, apA:galerkin(e), Frobenius uncertainty support.
Use: keep the actual Hilbert--Schmidt norm distinct from the spectral matrix norm;
the adjoint of a symmetric perturbation action is the symmetric outer product.
Source: reuse the earlier article's hsNorm/hsSq and ordinary Euclidean Cauchy--Schwarz.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
open scoped Matrix InnerProductSpace BigOperators
variable {n : ℕ}

/-- Flatten the actual matrix entries into their Euclidean Hilbert--Schmidt coordinates.
Use: import Hilbert-space Cauchy--Schwarz without changing the ambient matrix norm instance.
Article: main_krylov, apA:galerkin(e), Frobenius budgets. -/
def frobeniusVector (M : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij => M ij.1 ij.2)

/-- The flattened Euclidean norm is exactly the already defined Hilbert--Schmidt norm.
Use: the subsequent support theorem concerns the genuine Frobenius budget.
Article: main_krylov, apA:galerkin(e), ‖E‖_F.
Proof: both squared norms sum all actual squared entries, including the empty matrix. -/
theorem norm_frobeniusVector (M : Matrix (Fin n) (Fin n) ℝ) : ‖frobeniusVector M‖ = hsNorm M := by
  apply (sq_eq_sq₀ (norm_nonneg _) (hsNorm_nonneg M)).mp
  rw [hsNorm_sq, EuclideanSpace.real_norm_sq_eq]
  simp only [frobeniusVector, hsSq, Fintype.sum_prod_type]

/-- A flattened actual matrix vanishes exactly when all of its physical entries vanish.
Use: zero Frobenius budgets force the actual matrix perturbation to be zero.
Article: main_krylov, apA:galerkin(e).
Proof: evaluate the actual flattened equality at each entry coordinate. -/
theorem frobeniusVector_eq_zero_iff (M : Matrix (Fin n) (Fin n) ℝ) : frobeniusVector M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    exact congrArg (fun x : EuclideanSpace ℝ (Fin n × Fin n) => x (i, j)) h
  · rintro rfl
    ext ij
    rfl

/-- Flattening actual matrix entries commutes with real scalar multiplication.
Use: the attaining Frobenius perturbation is a scaled actual symmetric outer product.
Article: main_krylov, apA:galerkin(e).
Proof: the two vectors agree at every matrix-entry coordinate. -/
theorem frobeniusVector_smul (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    frobeniusVector (c • M) = c • frobeniusVector M := by ext i; rfl

/-- Flattening actual matrix entries preserves addition exactly.
Use: expand Hilbert--Schmidt energies of the actual planar attaining matrices.
Article: main_krylov, lem:aggregate, Frobenius sharpness.
Proof: evaluate the two flattened vectors at each actual entry. -/
theorem frobeniusVector_add (M N : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusVector (M + N) = frobeniusVector M + frobeniusVector N := by ext i; rfl

/-- The genuine Hilbert--Schmidt norm has the exact scalar homogeneity.
Use: verify the exact budget of the actual support witness, including a zero Riesz vector.
Article: main_krylov, apA:galerkin(e).
Proof: flatten the actual entries and use Euclidean norm homogeneity. -/
theorem hsNorm_smul (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : hsNorm (c • M) = |c| * hsNorm M := by
  rw [← norm_frobeniusVector, frobeniusVector_smul, norm_smul, norm_frobeniusVector, Real.norm_eq_abs]

/-- The true Frobenius inner product sums the entrywise products.
Use: identify symmetric action functionals with their actual Riesz vectors.
Article: main_krylov, apA:galerkin(e), Frobenius adjoint.
Proof: expand the Euclidean inner product in the product index set. -/
theorem inner_frobeniusVector (M N : Matrix (Fin n) (Fin n) ℝ) :
    inner ℝ (frobeniusVector M) (frobeniusVector N) = ∑ i, ∑ j, M i j * N i j := by
  simp only [frobeniusVector, EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct,
    Fintype.sum_prod_type, mul_comm]

/-- Actual outer-product matrices have the standard factorized Frobenius pairing.
Use: compute exact Frobenius budgets of the symmetric two-plane attaining families.
Article: main_krylov, lem:aggregate, Frobenius sharpness.
Proof: separate the two independent finite entry sums by distributivity. -/
theorem frobenius_outer_pairing (u v w z : Fin n → ℝ) :
    inner ℝ (frobeniusVector (vecMulVec u v)) (frobeniusVector (vecMulVec w z)) =
      (u ⬝ᵥ w) * (v ⬝ᵥ z) := by
  rw [inner_frobeniusVector]
  simp only [vecMulVec_apply]
  -- Separate the row index first, preserving the two actual coordinate pairings.
  calc
    _ = ∑ i, (u i * w i) * (∑ j, v j * z j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The symmetric outer product representing a symmetric perturbation action functional.
Use: its genuine Frobenius norm replaces the spectral support product ‖u‖‖v‖.
Article: main_krylov, apA:galerkin(e), sym(u⊗v). -/
def symmetricOuter (u v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (vecMulVec u v + vecMulVec v u)

/-- The action's Frobenius Riesz vector is genuinely symmetric.
Use: the Frobenius support witness remains inside the symmetric uncertainty class.
Article: main_krylov, apA:galerkin(e), symmetric Frobenius support.
Proof: transposition interchanges the two outer products. -/
theorem symmetricOuter_isSymm (u v : Fin n → ℝ) : (symmetricOuter u v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [symmetricOuter, Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, smul_eq_mul]
  ring

/-- The actual symmetric perturbation action pairs with its symmetric Frobenius Riesz vector.
Use: the exact single-increment adjoint formula in Frobenius budget duality.
Article: main_krylov, apA:galerkin(e), ⟨u,Ev⟩=⟨E,sym(u⊗v)⟩_F.
Proof: expand both outer-product pairings; swap the indices in the second and use Eᵀ=E. -/
theorem symmetric_action_frobenius (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm)
    (u v : Fin n → ℝ) :
    u ⬝ᵥ (E *ᵥ v) = inner ℝ (frobeniusVector E) (frobeniusVector (symmetricOuter u v)) := by
  rw [inner_frobeniusVector]
  have hswap : (∑ i, ∑ j, E i j * (v i * u j)) = ∑ i, ∑ j, E i j * (u i * v j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hE.apply i j]
    ring
  -- Keep the two outer terms separate until the transposed pairing has been identified.
  have hleft : u ⬝ᵥ (E *ᵥ v) = ∑ i, ∑ j, E i j * (u i * v j) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hleft]
  symm
  calc
    _ = ∑ i, ∑ j, ((1 / 2 : ℝ) * (E i j * (u i * v j)) +
        (1 / 2 : ℝ) * (E i j * (v i * u j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [symmetricOuter, Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, smul_eq_mul]
      ring
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, E i j * (u i * v j)) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, E i j * (v i * u j)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hswap]; ring

/-- The actual symmetric Frobenius ball has exactly the norm of the symmetric outer-product support.
Use: the sharp Frobenius replacement in full budget duality, with a real attaining matrix.
Article: main_krylov, apA:galerkin(e), max_E ⟨u,Ev⟩=Ω‖sym(u⊗v)‖_F.
Proof: Euclidean Cauchy--Schwarz bounds the actual Riesz pairing; scale that
same symmetric outer product to its budget, treating its zero norm explicitly. -/
theorem frobenius_ball_support (u v : Fin n → ℝ) {Ω : ℝ} (hΩ : 0 ≤ Ω) :
    IsGreatest {z : ℝ | ∃ E : Matrix (Fin n) (Fin n) ℝ,
      E.IsSymm ∧ hsNorm E ≤ Ω ∧ z = u ⬝ᵥ (E *ᵥ v)} (Ω * hsNorm (symmetricOuter u v)) := by
  let S := symmetricOuter u v
  let c := Ω * (hsNorm S)⁻¹
  have hc : 0 ≤ c := mul_nonneg hΩ (inv_nonneg.mpr (hsNorm_nonneg S))
  have hn : hsNorm (c • S) ≤ Ω := by
    rw [hsNorm_smul, abs_of_nonneg hc]
    by_cases hz : hsNorm S = 0
    · simp only [hz, mul_zero]; exact hΩ
    · change Ω * (hsNorm S)⁻¹ * hsNorm S ≤ Ω
      rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
  constructor
  · refine ⟨c • S, (symmetricOuter_isSymm u v).smul c, hn, ?_⟩
    rw [symmetric_action_frobenius _ ((symmetricOuter_isSymm u v).smul c),
      frobeniusVector_smul, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_frobeniusVector]
    change Ω * hsNorm S = (Ω * (hsNorm S)⁻¹) * hsNorm S ^ 2
    by_cases hz : hsNorm S = 0
    · simp [hz]
    · field_simp
  · rintro z ⟨E, hE, hnorm, rfl⟩
    -- The budget uses the actual flattened Euclidean norm, independently of matrix-norm scopes.
    rw [symmetric_action_frobenius E hE]
    have h := real_inner_le_norm (frobeniusVector E) (frobeniusVector S)
    rw [norm_frobeniusVector, norm_frobeniusVector] at h
    exact h.trans (mul_le_mul_of_nonneg_right hnorm (hsNorm_nonneg S))

end
end krylov.LinearAlgebra
