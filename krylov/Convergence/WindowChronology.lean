import krylov.Convergence.SS1Execution
import Mathlib.Data.List.OfFn

/-!
Article: main_krylov, thm:grow, passage from literal chronological memory
to the actual SS1 window. Source: elementary finite-list truncation.
Use: after one full clean window, every retained observation is exactly
one of the last accepted displacements, in the original chronological order.
This algebraic lemma is applied to the actual derived clean update.
-/

namespace krylov.Convergence
open List
variable {α : Type*}

/-- A clean append-and-retain execution forgets every preceding observation
after one full window. The conclusion is an equality of actual lists. -/
theorem chronological_window_flush (L : ℕ → List α) (a : ℕ → α) (n K : ℕ)
    (hlen : ∀ k,K≤k → n≤(L k).length)
    (hstep : ∀ k,K≤k → L (k+1)=(L k).drop ((L k).length-n)++[a k])
    (k : ℕ) (hk : K≤k) :
    (L (k+n)).drop ((L (k+n)).length-n)=List.ofFn (fun i : Fin n=>a (k+i.val)) := by
  have hh : ∀ j,j≤n → (L (k+j)).reverse.take j=
      (List.ofFn (fun i : Fin j=>a (k+i.val))).reverse := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hjn : j≤n := by omega
      have hlenj := hlen (k+j) (by omega)
      rw [show k+(j+1)=k+j+1 by omega,hstep (k+j) (by omega),List.reverse_append]
      simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.reverse_drop,
        Nat.sub_sub_self hlenj,List.take_succ_cons,List.take_take,min_eq_left hjn]
      rw [ih hjn,List.ofFn_succ']
      simp only [List.concat_eq_append,List.reverse_append,List.reverse_cons,List.reverse_nil,
        List.cons_append,List.nil_append,Fin.val_last,Fin.val_castSucc]
  apply List.reverse_injective
  rw [List.reverse_drop,Nat.sub_sub_self (hlen (k+n) (by omega))]
  exact hh n le_rfl

end krylov.Convergence
