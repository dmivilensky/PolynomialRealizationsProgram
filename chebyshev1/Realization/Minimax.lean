import chebyshev1.Realization.AffineExecution
import chebyshev1.Realization.Degree
import chebyshev1.Background.Minimax

/-! Chebyshev minimax lower bound for the actual fixed-coefficient realization. -/
namespace chebyshev1.Realization
noncomputable section
open Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Affine consistency and N gradient calls imply the interval minimax lower bound. -/
theorem residual_minimax_lower (R : Realization ι) (I : SpectralInterval) {N : ℕ}
    (h : R.AffineConsistent N) (B : ℝ)
    (hB : ∀ lam ∈ Set.Icc I.mu I.L, |(R.residualPolynomial N).eval lam| ≤ B) :
    I.epsilon N ≤ B := by
  let a : ℝ[X] := C ((I.L + I.mu) / 2) - C (I.delta / 2) * X
  have ha : a.natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  have heval (x : ℝ) : a.eval x = I.lambda x := by
    simp [a, SpectralInterval.lambda]
  have heta : a.eval I.eta = 0 := by
    rw [heval]
    dsimp [SpectralInterval.lambda, SpectralInterval.eta]
    field_simp [I.delta_pos.ne']
    ring
  apply chebyshev_minimax_lower I.eta I.eta_gt_one N ((R.residualPolynomial N).comp a)
  · exact natDegree_comp_le.trans
      ((Nat.mul_le_mul (R.residualPolynomial_natDegree_le N) ha).trans (by simp))
  · simpa only [eval_comp, heta] using h.residual_zero
  · intro x hx
    simpa only [eval_comp, heval] using hB (I.lambda x) (I.lambda_mem hx)

end
end chebyshev1.Realization
