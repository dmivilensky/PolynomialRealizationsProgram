import chebyshev2.Green.Bidiagonal
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Article: chebyshev2, Theorem A.1.
Odd/even grouping, with zero-based even indices representing the paper's odd sites.
Use: `chebyshev2.Centering.interleave` feeds `chebyshev2.Centering.lift_compression` (lift
compression).
Proof chain: `chebyshev2.Jacobi.lift_grouped_matrix` — chebyshev2, Theorem A.1; Centering
lift, contractivity, odd Green entries and characteristic polynomial.
-/
namespace chebyshev2.Centering
variable (N : ℕ)

/--
Odd/even grouping, with zero-based even indices representing the paper's odd sites.

Use: `chebyshev2.Centering.interleave` uses this definition in the displayed construction
of `interleave`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_grouped_matrix`.
-/
def groupPairs : Fin N ⊕ Fin N ≃ Fin N × Fin 2 where
  toFun := Sum.elim (fun i => (i,0)) (fun i => (i,1))
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv i := by cases i <;> simp
  right_inv p := by rcases p with ⟨i,j⟩; fin_cases j <;> simp

/--
Defines `interleave` of type `Fin N ⊕ Fin N ≃ Fin (2*N)` by `(groupPairs N).trans
(finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2)))`.

Use: `chebyshev2.Centering.interleave_left` rewrites with this definition to establish
exact identity `(interleave N (Sum.inl i)).val = 2*i.val`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_grouped_matrix`.
-/
def interleave : Fin N ⊕ Fin N ≃ Fin (2*N) :=
  (groupPairs N).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2)))

/--
Exact identity `(interleave N (Sum.inl i)).val = 2*i.val`.

Use: `chebyshev2.Centering.grouped_matrix` rewrites with this identity to establish exact
identity `C.matrix.submatrix (interleave N) (interleave N) = blockLift (extractedBlock C)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_grouped_matrix`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem interleave_left (i : Fin N) :
    (interleave N (Sum.inl i)).val = 2*i.val := by simp [interleave,groupPairs]

/--
Exact identity `(interleave N (Sum.inr i)).val = 2*i.val+1`.

Use: `chebyshev2.Centering.grouped_matrix` rewrites with this identity to establish exact
identity `C.matrix.submatrix (interleave N) (interleave N) = blockLift (extractedBlock C)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_grouped_matrix`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem interleave_right (i : Fin N) :
    (interleave N (Sum.inr i)).val = 2*i.val+1 := by simp [interleave,groupPairs,Nat.add_comm]

end chebyshev2.Centering
