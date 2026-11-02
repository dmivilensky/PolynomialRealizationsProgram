import krylov.Convergence.OrderCounting

/-!
Article: main_krylov, Table s7-orders, finite observed history.
Use: count literal gradient queries after any finite initialization prefix.
Source: the exact exponential barrier and finite positive powers.
-/
namespace krylov.Convergence
noncomputable section

/-- Deleting a finite actual prefix preserves the same R-order, with a
new genuine geometric base. -/
theorem HasROrder.shift {e : ℕ → ℝ} {τ : ℝ} (h : HasROrder e τ)
    (hτ : 0<τ) (N : ℕ) : HasROrder (fun k=>e (k+N)) τ := by
  obtain ⟨C,q,hC,hq,hq₁,hbound⟩ := h
  refine ⟨C,q^(τ^N),hC,Real.rpow_pos_of_pos hq _,
    Real.rpow_lt_one hq.le hq₁ (pow_pos hτ N),?_⟩
  intro k
  have hh := hbound (k+N)
  rw [←Real.rpow_mul hq.le]
  simpa only [pow_add,mul_comm] using hh

end
end krylov.Convergence
