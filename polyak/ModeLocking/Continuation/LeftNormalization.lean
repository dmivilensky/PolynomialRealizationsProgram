import polyak.ModeLocking.Continuation.LeftKernel

/-! Replacing one redundant left-kernel equation by its class-mass
normalization gives an invertible square system. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def normalizationIndex : Fin D.d := ⟨0, D.d_pos⟩

def leftNormalMatrix : Matrix (Fin D.d) (Fin D.d) ℝ :=
  fun i r => if i = D.normalizationIndex then 1 else D.matrix r i

theorem right_kernel_annihilates (v : Fin D.d → ℝ) :
    (∑ i, (D.primal i : ℝ) * D.matrix.transpose.mulVec v i) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  have hrow := congrFun D.matrix_mul_primal r
  change (∑ i, D.matrix r i * (D.primal i : ℝ)) = 0 at hrow
  calc
    ∑ i, (D.primal i : ℝ) * (D.matrix r i * v r) =
      (∑ i, D.matrix r i * (D.primal i : ℝ)) * v r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = 0 := by rw [hrow, zero_mul]

theorem leftNormalMatrix_injective : Function.Injective D.leftNormalMatrix.mulVec := by
  apply (injective_iff_map_eq_zero D.leftNormalMatrix.mulVecLin).mpr
  intro v hv
  have hnorm := congrFun hv D.normalizationIndex
  change (∑ r, D.leftNormalMatrix D.normalizationIndex r * v r) = 0 at hnorm
  simp [leftNormalMatrix] at hnorm
  have hother (i : Fin D.d) (hi : i ≠ D.normalizationIndex) : D.matrix.transpose.mulVec v i = 0 := by
    have hh := congrFun hv i
    change (∑ r, D.leftNormalMatrix i r * v r) = 0 at hh
    simpa only [leftNormalMatrix, ite_eq_right hi, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply] using hh
  have hmissing : D.matrix.transpose.mulVec v D.normalizationIndex = 0 := by
    have hsum := D.right_kernel_annihilates v
    have hterm : (∑ i, (D.primal i : ℝ) * D.matrix.transpose.mulVec v i) =
        (D.primal D.normalizationIndex : ℝ) * D.matrix.transpose.mulVec v D.normalizationIndex := by
      apply Finset.sum_eq_single D.normalizationIndex
      · intro i _ hi
        rw [hother i hi, mul_zero]
      · simp
    rw [hterm] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left (by exact_mod_cast (D.primal_pos _).ne')
  have hall : D.matrix.transpose.mulVec v = 0 := by
    funext i
    change D.matrix.transpose.mulVec v i = 0
    by_cases hi : i = D.normalizationIndex
    · rw [hi, hmissing]
    · exact hother i hi
  obtain ⟨c, hc⟩ := D.left_kernel_unique hall
  have hsum : c * (∑ i, D.classWeight i) = 0 := by
    rw [Finset.mul_sum]
    simpa only [hc] using hnorm
  have hcz : c = 0 := (mul_eq_zero.mp hsum).resolve_right D.classWeight_sum_pos.ne'
  funext i
  change v i = 0
  rw [hc, hcz, zero_mul]

def leftNormalEquiv : (Fin D.d → ℝ) ≃L[ℝ] (Fin D.d → ℝ) :=
  (LinearEquiv.ofBijective D.leftNormalMatrix.mulVecLin
    ⟨D.leftNormalMatrix_injective, LinearMap.surjective_of_injective D.leftNormalMatrix_injective⟩).toContinuousLinearEquiv

end polyak.ModeLocking.RegularData
