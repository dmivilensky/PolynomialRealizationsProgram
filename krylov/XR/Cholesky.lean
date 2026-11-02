import krylov.XR.CholeskySchur
import krylov.XR.HermitianNorm

/-!
Article: main_krylov, prop:cert, exact finite Cholesky realization.
Use: compute the actual successive Schur pivots of the reversed Hermitian
window and prove that their strict positivity is exactly the original
test. Restricting to actual suffixes gives the same maximal retained
window as the existing finite selection. Source: proved strict Schur
extension and principal-submatrix positivity.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped ComplexOrder Matrix

/-- The actual leading block before the last Cholesky extension.
Article: main_krylov, prop:cert. -/
def choleskyLeading {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := H.submatrix Fin.castSucc Fin.castSucc

/-- The actual newly appended Hermitian cross column. Article: prop:cert. -/
def choleskyColumn {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Matrix (Fin n) (Fin 1) ℂ := fun i _=>H i.castSucc (Fin.last n)

/-- The actual new diagonal, before elimination. Article: prop:cert. -/
def choleskyDiagonal {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Matrix (Fin 1) (Fin 1) ℂ := fun _ _=>H (Fin.last n) (Fin.last n)

/-- The original matrix, with its last index split off, is exactly the
block input of the proved Schur criterion. Article: prop:cert. -/
theorem cholesky_split_last {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hH : H.IsHermitian) :
    H.submatrix (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1)) finSumFinEquiv=
      fromBlocks (choleskyLeading H) (choleskyColumn H) (choleskyColumn H)ᴴ (choleskyDiagonal H) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => fin_cases j; rfl
  | inr i =>
    fin_cases i
    cases j with
    | inl j =>
      change H (Fin.last n) j.castSucc=star (H j.castSucc (Fin.last n))
      exact (congrFun (congrFun hH.eq (Fin.last n)) j.castSucc).symm
    | inr j => fin_cases j; rfl

/-- Actual principal reindexing preserves strict positivity in both
directions. Article: main_krylov, prop:cert. -/
theorem posDef_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (H.submatrix e e).PosDef ↔ H.PosDef := by
  refine ⟨fun h=>?_,fun h=>h.submatrix e.injective⟩
  simpa only [submatrix_submatrix,Equiv.self_comp_symm,submatrix_id_id] using h.submatrix e.symm.injective

/-- The genuine last Cholesky extension is governed by its actual Schur
pivot. Article: main_krylov, prop:cert. -/
theorem cholesky_last_iff {n : ℕ} (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hH : H.IsHermitian) (hA : (choleskyLeading H).PosDef) :
    H.PosDef ↔ 0<schurPivot (choleskyLeading H) (choleskyColumn H) (choleskyDiagonal H) := by
  rw [←posDef_submatrix_equiv H finSumFinEquiv,cholesky_split_last H hH]
  exact cholesky_extension_iff _ _ _ hA

/-- Strict positivity of every genuine successive Schur pivot, computed
from actual leading matrices. This is the exact-arithmetic sign test for
squared Cholesky diagonals; its empty case passes. Article: prop:cert. -/
def choleskyPass : {n : ℕ} → Matrix (Fin n) (Fin n) ℂ → Prop
  | 0,_ => True
  | _+1,H => choleskyPass (choleskyLeading H) ∧
      0<schurPivot (choleskyLeading H) (choleskyColumn H) (choleskyDiagonal H)

/-- Success of the actual complete pivot calculation is equivalent to
the original strict Hermitian test, with all leading inverse domains
proved by induction. Article: main_krylov, prop:cert. -/
theorem choleskyPass_iff_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) : choleskyPass H ↔ H.PosDef := by
  induction n with
  | zero =>
    have he : H=1 := Subsingleton.elim _ _
    simp only [choleskyPass,true_iff,he]
    exact PosDef.one
  | succ n ih =>
    change (choleskyPass (choleskyLeading H) ∧ 0<schurPivot _ _ _) ↔ _
    rw [ih (choleskyLeading H) (hH.submatrix Fin.castSucc)]
    constructor
    · rintro ⟨hA,hp⟩
      exact (cholesky_last_iff H hH hA).mpr hp
    · intro hp
      have hA : (choleskyLeading H).PosDef := hp.submatrix (Fin.castSucc_injective n)
      exact ⟨hA,(cholesky_last_iff H hH hA).mp hp⟩

/-- The actual latest/skew window matrix is genuinely Hermitian even
at a totalized zero threshold. Article: main_krylov, prop:cert. -/
theorem hermitianWindowMatrix_isHermitian {p : ℕ} (theta : ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) : (hermitianWindowMatrix theta M).IsHermitian := by
  apply (ofReal_isHermitian (latest M) (latest_isSymm M)).add
  ext i j
  have hd : defect M j i= -defect M i j :=
    congrFun (congrFun (defect_transpose M) i) j
  change star ((Complex.I/(theta : ℂ))*Complex.ofReal (defect M j i))=
    (Complex.I/(theta : ℂ))*Complex.ofReal (defect M i j)
  rw [hd,Complex.ofReal_neg]
  simp
  ring

/-- The true reverse-index Cholesky pivot calculation used for suffix
retention. Article: main_krylov, prop:cert. -/
def reversedWindowCholesky {p : ℕ} (theta : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  choleskyPass ((hermitianWindowMatrix theta M).submatrix Fin.rev Fin.rev)

/-- The original Hermitian refutation test and the actual reversed
Cholesky pivot test are exactly equivalent. Article: prop:cert. -/
theorem reversedWindowCholesky_iff {p : ℕ} (theta : ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) : reversedWindowCholesky theta M ↔ windowUnrefuted theta M := by
  rw [reversedWindowCholesky,choleskyPass_iff_posDef _
    ((hermitianWindowMatrix_isHermitian theta M).submatrix Fin.rev)]
  exact posDef_submatrix_equiv _ Fin.revPerm

/-- The longest retained suffix is also exactly the one selected by the
actual reversed pivot test, and every longer suffix fails that test.
Article: main_krylov, prop:cert, Cholesky suffix selection. -/
theorem unrefutedSuffix_cholesky {p : ℕ} (theta : ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) :
    let o := unrefutedSuffix theta M
    o≤p ∧ reversedWindowCholesky theta (windowSuffix M o) ∧
      ∀ j<o,¬reversedWindowCholesky theta (windowSuffix M j) := by
  dsimp only
  obtain ⟨ho,hpass⟩ := unrefutedSuffix_spec theta M
  refine ⟨ho,(reversedWindowCholesky_iff theta _).mpr hpass,?_⟩
  intro j hj hp
  have hh := unrefutedSuffix_minimal theta M j (hj.le.trans ho)
    ((reversedWindowCholesky_iff theta _).mp hp)
  omega

end
end krylov.XR
