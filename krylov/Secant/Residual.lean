import krylov.Secant.Flag
import krylov.Secant.Correction
import Mathlib.Tactic.Abel

/-!
Article: Lemma A.4 [lem:transfer] of krylov.tex.
Use: transfer observed secant defects to the terminal or sliding-window gradient.
These exact identities require only the stated line orthogonality and retained
pair conjugacy; they make no assumption about a perturbation expansion.
Source: finite telescoping of actual gradient updates.
-/

namespace krylov.Secant
open Matrix Finset
open scoped Matrix BigOperators
variable {n : ℕ}

/-- Telescoping the actual secant updates gives the gradient difference.
Use: the staircase proof starts at the exact line search of the retained pair.
Article: main_krylov, lem:transfer.
Proof: replace each secant by its actual gradient difference and telescope. -/
theorem gradient_difference (g y : ℕ → Fin n → ℝ)
    (hy : ∀ j, g (j + 1) = g j + y j) {a b : ℕ} (hab : a ≤ b) :
    g b - g a = ∑ j ∈ Ico a b, y j := by
  rw [← Finset.sum_Ico_sub g hab]
  apply Finset.sum_congr rfl
  intro j _
  rw [hy j]
  abel

/-- A line-search residual is the sum of all subsequently observed secant actions.
Use: the exact staircase formula before imposing full conjugacy.
Article: main_krylov, lem:transfer, first displayed identity.
Proof: pair the telescoped updates with the old step, whose line residual is zero. -/
theorem staircase_residual (g y s : ℕ → Fin n → ℝ)
    (hy : ∀ j, g (j + 1) = g j + y j) {i N : ℕ} (hiN : i < N)
    (hline : s i ⬝ᵥ g (i + 1) = 0) :
    s i ⬝ᵥ g N = ∑ j ∈ Ico (i + 1) N,
      ((s i ⬝ᵥ y j - s j ⬝ᵥ y i) + s j ⬝ᵥ y i) := by
  have h := congrArg (fun v => s i ⬝ᵥ v)
    (gradient_difference g y hy (Nat.succ_le_of_lt hiN))
  simpa only [dotProduct_sub, hline, sub_zero, dotProduct_sum, sub_add_cancel] using h

/-- Retaining an old FC pair leaves precisely its accumulated newer defects.
Use: applies to either a full cycle or a retained suffix in a sliding window.
Article: main_krylov, lem:transfer, exact full-conjugacy staircase.
Proof: the retained conjugacy equations annihilate the older-operator terms. -/
theorem conjugate_staircase (g y s : ℕ → Fin n → ℝ)
    (hy : ∀ j, g (j + 1) = g j + y j) {i N : ℕ} (hiN : i < N)
    (hline : s i ⬝ᵥ g (i + 1) = 0)
    (hconj : ∀ j ∈ Ico (i + 1) N, s j ⬝ᵥ y i = 0) :
    s i ⬝ᵥ g N = ∑ j ∈ Ico (i + 1) N, (s i ⬝ᵥ y j - s j ⬝ᵥ y i) := by
  rw [staircase_residual g y s hy hiN hline]
  exact Finset.sum_congr rfl fun j hj => by rw [hconj j hj, add_zero]

/-- The antisymmetric pairing is exactly the difference between two segment operators.
Use: connects the residual staircase with physical Hessian variation.
Article: main_krylov, lem:transfer, D_ij = sᵢᵀ(Aⱼ−Aᵢ)sⱼ.
Proof: move the symmetric older operator across the scalar pairing. -/
theorem physical_defect (s : ℕ → Fin n → ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k, (A k).IsSymm) (i j : ℕ) :
    s i ⬝ᵥ (A j *ᵥ s j) - s j ⬝ᵥ (A i *ᵥ s i) =
      s i ⬝ᵥ ((A j - A i) *ᵥ s j) := by
  rw [sub_mulVec, dotProduct_sub]
  congr 1
  rw [dotProduct_mulVec, ← (hA i).eq, vecMul_transpose, dotProduct_comm, (hA i).eq]

/-- Invertible step coordinates reconstruct the physical residual uniquely.
Use: specializes to old-step residuals and a zero coordinate for the last search.
Article: main_krylov, lem:recon, g = S⁻ᵀr.
Proof: apply the inverse transpose to the given coordinate identity. -/
theorem residual_reconstruction (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) (g r : Fin n → ℝ) (hr : Sᵀ *ᵥ g = r) :
    g = Sᵀ⁻¹ *ᵥ r := by
  rw [← hr, mulVec_mulVec, nonsing_inv_mul _ (by simpa only [det_transpose] using hS),
    one_mulVec]

end krylov.Secant
