import polyak.Numerics.Parametric.Basic

/-! Exact finite materialization avoids repeated interval evaluations. -/
namespace polyak.Numerics.Parametric

@[noinline] def memoFin {n : ℕ} {α : Type*} (f : Fin n → α) : Fin n → α :=
  let values := List.ofFn f
  fun i => values[i.val]'(by simpa only [values,List.length_ofFn] using i.isLt)

theorem memoFin_eq {n : ℕ} {α : Type*} (f : Fin n → α) : memoFin f=f := by
  funext i
  simp [memoFin]

@[noinline] def memoMatrix {n : ℕ} {α : Type*} (f : Matrix (Fin n) (Fin n) α) :
    Matrix (Fin n) (Fin n) α := memoFin (fun i => memoFin (fun j => f i j))

theorem memoMatrix_eq {n : ℕ} {α : Type*} (f : Matrix (Fin n) (Fin n) α) : memoMatrix f=f := by
  funext i j
  simp only [memoMatrix,memoFin_eq]

end polyak.Numerics.Parametric
