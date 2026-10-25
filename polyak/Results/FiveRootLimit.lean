import polyak.Results.FiveDimensionalActual
import polyak.Results.RootLimit

/-! Article: the original five-dimensional finite-horizon worst cases have
the same genuine root limit as the unrestricted exact rate. -/
namespace polyak.Results
noncomputable section
open Filter Dynamics Spectral
open scoped Topology

theorem tendsto_worst_five_root {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    Tendsto (fun n : ℕ => worst μ L (polyakAlpha μ L) (polyakBeta μ L) 5 n^((n : ℝ)⁻¹))
      atTop (𝓝 (Real.exp (T (polyakQ μ L)))) := by
  obtain ⟨a,ha,hlower⟩:=exists_worst_five_optimal_lower hμ hL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (prefactor_root_tendsto ha (T (polyakQ μ L))) (tendsto_worstAll_root hμ hL)
    (prefactor_root_le ha hlower)
  exact Eventually.of_forall fun n => Real.rpow_le_rpow
    (worst_nonneg hμ hL (polyakAlpha_pos hμ hL).le (polyakBeta_mem hμ hL).1 5 n)
    (worst_le_worstAll hμ hL (polyakAlpha_pos hμ hL).le (polyakBeta_mem hμ hL).1 (by norm_num) n)
    (by positivity)

end
end polyak.Results
