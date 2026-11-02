import krylov.XR.CholeskyCount

/-!
Article: main_krylov, prop:cert and alg:cert, actual one-pass suffix selection.
Use: identify p minus the number of genuine positive reversed Cholesky
pivots with the original longest admissible chronological suffix.
Source: exact reversed-prefix/chronological-suffix indexing and the proved
first-failure counter; no independent admissibility certificate is supplied.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped ComplexOrder
variable {p : ℕ}

/-- Reversed leading blocks are exactly reversed chronological suffixes
of the actual Hermitian window matrix. Article: prop:cert. -/
theorem reversed_window_initial (theta : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (o : ℕ) :
    choleskyInitial ((hermitianWindowMatrix theta M).submatrix Fin.rev Fin.rev)
      (p-o) (Nat.sub_le p o)=
      (hermitianWindowMatrix theta (windowSuffix M o)).submatrix Fin.rev Fin.rev := by
  have hf (i : Fin (p-o)) : Fin.rev (Fin.castLE (Nat.sub_le p o) i)=windowSuffixIndex p o (Fin.rev i) := by
    apply Fin.ext
    simp only [Fin.val_rev,Fin.val_castLE,windowSuffixIndex]
    have hi := i.isLt
    omega
  rw [windowSuffix,hermitianWindowMatrix_submatrix theta M _ (windowSuffixIndex_strictMono p o)]
  ext i j
  simp only [choleskyInitial,submatrix_apply,hf]

/-- The original suffix at offset o passes exactly when its length
does not exceed the actual number of positive reversed pivots.
Article: main_krylov, prop:cert, first failing pivot. -/
theorem windowSuffix_choleskyCount_iff (theta : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (o : ℕ) :
    windowUnrefuted theta (windowSuffix M o) ↔
      p-o≤choleskyPositiveCount ((hermitianWindowMatrix theta M).submatrix Fin.rev Fin.rev) := by
  rw [←reversedWindowCholesky_iff,reversedWindowCholesky,←reversed_window_initial,
    choleskyInitial_pass_iff]

/-- The literal one-pass implementation returns p-j after exactly j
positive pivots and stops before testing a pivot past the first failure.
Article: main_krylov, alg:cert, UnrefutedSuffix. -/
def unrefutedSuffixByCholesky (theta : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) : ℕ :=
  p-choleskyPositiveCount ((hermitianWindowMatrix theta M).submatrix Fin.rev Fin.rev)

/-- The actual early-stopping Cholesky implementation equals the
original longest admissible suffix search, including empty/all-passing
windows. Article: main_krylov, prop:cert and alg:cert. -/
theorem unrefutedSuffixByCholesky_eq (theta : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) :
    unrefutedSuffixByCholesky theta M=unrefutedSuffix theta M := by
  let j := choleskyPositiveCount ((hermitianWindowMatrix theta M).submatrix Fin.rev Fin.rev)
  have hj : j≤p := choleskyPositiveCount_le _
  have hpass : windowUnrefuted theta (windowSuffix M (p-j)) :=
    (windowSuffix_choleskyCount_iff theta M (p-j)).mpr (by change p-(p-j)≤j;omega)
  have hmin := unrefutedSuffix_minimal theta M (p-j) (Nat.sub_le p j) hpass
  have hs := unrefutedSuffix_spec theta M
  have hlen := (windowSuffix_choleskyCount_iff theta M (unrefutedSuffix theta M)).mp hs.2
  change p-j=unrefutedSuffix theta M
  change p-unrefutedSuffix theta M≤j at hlen
  omega

end
end krylov.XR
