import krylov.XR.Cholesky

/-!
Article: main_krylov, prop:cert, literal first-failing-pivot execution.
Use: compute the number of successive positive pivots with an actual
early stop. No pivot after a failed leading block is evaluated.
Source: the proved strict Schur Cholesky criterion, including empty blocks.
-/
namespace krylov.XR
noncomputable section
open Matrix
open scoped ComplexOrder

/-- Exact first-failure Cholesky counter. The recursive leading block
is factored first; only its complete success permits the next pivot.
Article: main_krylov, prop:cert, j positive pivots. -/
def choleskyPositiveCount : {n : ℕ} → Matrix (Fin n) (Fin n) ℂ → ℕ
  | 0,_ => 0
  | n+1,H => by
    classical
    exact if choleskyPositiveCount (choleskyLeading H)=n then
      if 0<schurPivot (choleskyLeading H) (choleskyColumn H) (choleskyDiagonal H) then n+1 else n
      else choleskyPositiveCount (choleskyLeading H)

/-- The literal first-failure counter never exceeds the matrix size.
Article: main_krylov, prop:cert. -/
theorem choleskyPositiveCount_le {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    choleskyPositiveCount H≤n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hh := ih (choleskyLeading H)
    dsimp only [choleskyPositiveCount]
    split_ifs <;> omega

/-- All pivots were accepted exactly when the actual full recursive
Cholesky calculation passes. Article: main_krylov, prop:cert. -/
theorem choleskyPositiveCount_full_iff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    choleskyPositiveCount H=n ↔ choleskyPass H := by
  induction n with
  | zero => simp only [choleskyPositiveCount,choleskyPass]
  | succ n ih =>
    rw [choleskyPass,←ih (choleskyLeading H)]
    have hh := choleskyPositiveCount_le (choleskyLeading H)
    dsimp only [choleskyPositiveCount]
    split_ifs <;> simp_all
    omega

/-- The actual leading physical block of any prescribed admissible
size. Article: main_krylov, prop:cert. -/
def choleskyInitial {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (hk : k≤n) :
    Matrix (Fin k) (Fin k) ℂ := H.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- The full initial block is literally the original matrix.
Article: main_krylov, prop:cert. -/
theorem choleskyInitial_self {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    choleskyInitial H n le_rfl=H := by ext i j;rfl

/-- Taking an initial block commutes with removing the final row and
column. Article: main_krylov, prop:cert. -/
theorem choleskyInitial_leading {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (k : ℕ) (hk : k≤n) (hk' : k≤n+1) :
    choleskyInitial (choleskyLeading H) k hk=choleskyInitial H k hk' := by ext i j;rfl

/-- A prescribed leading block passes exactly when its size does not
exceed the number of actually accepted pivots. This characterizes the
first failure and every successful prefix of the one-pass execution.
Article: main_krylov, prop:cert. -/
theorem choleskyInitial_pass_iff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) (hk : k≤n) :
    choleskyPass (choleskyInitial H k hk) ↔ k≤choleskyPositiveCount H := by
  induction n with
  | zero =>
    have he : k=0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp only [choleskyPass,choleskyPositiveCount,le_refl]
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      rw [choleskyInitial_self,←choleskyPositiveCount_full_iff]
      have hh := choleskyPositiveCount_le H
      omega
    · have hk' : k≤n := by omega
      rw [←choleskyInitial_leading H k hk' hk,ih (choleskyLeading H) hk']
      have hh := choleskyPositiveCount_le (choleskyLeading H)
      dsimp only [choleskyPositiveCount]
      split_ifs <;> omega

end
end krylov.XR
