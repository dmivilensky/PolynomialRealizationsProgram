import nesterov.Smooth.Execution
import nesterov.Momentum.Stationary

/-! Article: Remark `rem:uniform-smoothness`.
Use: actual momentum iterates from the same rest start converge under uniformly
approximating gradient oracles. -/
namespace nesterov.Smooth
noncomputable section
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Source momentum iterates inherit finite-prefix continuity, including the
unchanged from-rest initialization. -/
theorem momentum_iterate_tendsto {ι : Type*} {l : Filter ι}
    {g : E → E} (hg : Continuous g) {a : ι → E → E} {err : ι → ℝ}
    (he : Tendsto err l (𝓝 0)) (ha : ∀ i x, ‖a i x-g x‖ ≤ err i)
    (β τ h : ℝ) (hh : h ≠ 0) (x₀ : E) (n : ℕ) :
    Tendsto (fun i => Momentum.iterate (a i) β τ h x₀ n) l
      (𝓝 (Momentum.iterate g β τ h x₀ n)) := by
  let M := Momentum.method β τ h hh
  let initial : Fin M.memory → E := fun _ => x₀
  have hhistory (b : E → E) : Momentum.history b β τ h x₀ x₀=M.run b initial := by
    apply StationaryMethod.IsTrajectory.unique M
      (Momentum.history_isTrajectory b β τ h hh x₀ x₀) (M.run_isTrajectory b initial)
    intro j
    rw [M.run_initial]
    change Momentum.history b β τ h x₀ x₀ (j:ℕ)=x₀
    fin_cases j <;> rfl
  have hp := run_tendsto M hg he ha initial (n+1)
  simpa only [← hhistory, Momentum.history,Momentum.iterate,Momentum.restState] using hp

end
end nesterov.Smooth
