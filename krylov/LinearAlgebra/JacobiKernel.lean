import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine Jacobi endpoint nonvanishing.
Use: exclude an actual null vector with zero final coordinate using the original nonzero tridiagonal edges.
Source: elementary backward substitution in the actual finite three-diagonal matrix.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped BigOperators
variable {N : ℕ}

/-- An actual irreducible tridiagonal null vector with genuine zero final coordinate is zero.
Use: An actual irreducible tridiagonal null vector with genuine zero final coordinate is zero.
Article: main_krylov, prop:phi(a), genuine Jacobi endpoint nonvanishing.
Proof: Propagate the genuine zero tail backwards; each original matrix row leaves exactly one real nonzero adjacent coefficient. -/
theorem tridiagonal_kernel_last (M : Matrix (Fin N) (Fin N) ℝ)
    (htri : ∀ i j : Fin N,i.val+1 < j.val ∨ j.val+1 < i.val → M i j=0)
    (hedge : ∀ i j : Fin N,i.val+1=j.val → M j i≠0)
    (x : Fin N → ℝ) (hx : M *ᵥ x=0) (hlast : ∀ i : Fin N,i.val+1=N → x i=0) : x=0 := by
  -- Each true backward row equation recovers the next earlier coordinate from the already zero physical tail.
  have htail (p : ℕ) : ∀ i : Fin N,N-p≤ i.val → x i=0 := by
    induction p with
    | zero =>
      intro i hi
      omega
    | succ p ih =>
      intro i hi
      by_cases ht : N-p≤ i.val
      · exact ih i ht
      by_cases hl : i.val+1=N
      · exact hlast i hl
      have hir : i.val+1<N := by omega
      let r : Fin N := ⟨i.val+1,hir⟩
      -- All actual row terms except the genuine preceding site vanish by the true band or the established zero tail.
      have hs : (∑ k : Fin N,M r k*x k)=M r i*x i := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          by_cases hk : k.val< i.val
          · have hm : M r k=0 := htri r k (Or.inr (by dsimp only [r];omega))
            rw [hm,zero_mul]
          · have hv : x k=0 := ih k (by
              have hne : k.val≠i.val := fun h => hki (Fin.ext h)
              omega)
            rw [hv,mul_zero]
        · intro h
          exact False.elim (h (Finset.mem_univ i))
      have hz := congrFun hx r
      change (∑ k : Fin N,M r k*x k)=0 at hz
      rw [hs] at hz
      exact (mul_eq_zero.mp hz).resolve_left (hedge i r rfl)
  ext i
  exact htail N i (by omega)
end
end krylov.LinearAlgebra
