import krylov.Cancellation.ResidualPropagation
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), consistent-estimate fresh-only products.
Use: simplify the genuine finite residual expansion when every reference
estimate equals its actual reference searched line length.
Source: exact finite products with zero reference multipliers and the actual
chronological final defect index; no residual cancellation is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open scoped BigOperators

/-- Consistent true reference estimates annihilate all old chronological
product terms and retain precisely the newest physical defect.
Use: combine with the actual compact reference-weight residual expansion;
its true remainder is quadratic under primitive C-one data.
Article: main_krylov, thm:dcs(c), consistent estimates leave the fresh defect alone.
Proof: every older product contains the actual final zero multiplier. Only
the newest index has an empty product, whose true value is one. -/
theorem consistent_residual_products (alpha a d : ℕ → ℝ) (N : ℕ) (hN : 0<N)
    (ha : ∀ l<N,a l≠0) (hconsistent : ∀ l<N,alpha l=a l) :
    (∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,(1-alpha l/a l))*d j)=d (N-1) := by
  calc
    _=(∏ l∈Finset.Ico ((N-1)+1) N,(1-alpha l/a l))*d (N-1) := by
      apply Finset.sum_eq_single (N-1)
      · intro j hj hne
        have hjN := Finset.mem_range.mp hj
        have hlast : N-1∈Finset.Ico (j+1) N := by simp only [Finset.mem_Ico];omega
        have hz : (∏ l∈Finset.Ico (j+1) N,(1-alpha l/a l))=0 := by
          apply Finset.prod_eq_zero hlast
          rw [hconsistent (N-1) (by omega),div_self (ha (N-1) (by omega)),sub_self]
        rw [hz,zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    _=d (N-1) := by
      rw [show (N-1)+1=N by omega,Finset.Ico_self,Finset.prod_empty,one_mul]

end
end krylov.Cancellation
