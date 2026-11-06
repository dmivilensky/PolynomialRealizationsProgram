import chebyshev1.Prefix.Kernel

/-! The first prefix query transmits a perturbation with endpoint coefficient N. -/
namespace chebyshev1.Prefix
noncomputable section
open Polynomial Polynomial.Chebyshev

theorem first_step_transmission (I : SpectralInterval) {N : ℕ} (hN : 0 < N) (nu : ℝ) :
    (realization I).kernel N 0 I.mu nu = -(2 * I.epsilon N / I.delta) * (N : ℝ) := by
  rw [kernel_zero I N (by omega), I.z_mu, U_eval_one]
  push_cast
  dsimp only [SpectralInterval.epsilon]
  ring

end
end chebyshev1.Prefix
