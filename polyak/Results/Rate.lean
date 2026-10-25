import polyak.Results.FiveRootLimit
import polyak.FiniteHorizon.GlobalPrefactor

/-!
Article: Theorem rate, both root limits and the uniform all-horizon bounds.
Use: the original function and from-rest start are fixed for every horizon.
The lower and upper bounds share the actual rate, uniformly in the dimension.
-/
noncomputable section
namespace polyak.Results
open Dynamics Spectral Filter
open scoped Topology

theorem exact_rate_root_limits {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    Tendsto (fun n : ℕ => worstAll μ L (polyakAlpha μ L) (polyakBeta μ L) n^((n : ℝ)⁻¹))
      atTop (𝓝 (rate μ L (polyakAlpha μ L) (polyakBeta μ L))) ∧
    Tendsto (fun n : ℕ => worst μ L (polyakAlpha μ L) (polyakBeta μ L) 5 n^((n : ℝ)⁻¹))
      atTop (𝓝 (rate μ L (polyakAlpha μ L) (polyakBeta μ L))) := by
  rw [originalRate_eq_exp_T hμ hL]
  exact ⟨tendsto_worstAll_root hμ hL,tendsto_worst_five_root hμ hL⟩

theorem exact_rate_all_horizon_bounds {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ c C : ℝ,0<c ∧ c≤C ∧ 0<C ∧
      ∃ f : EuclideanSpace ℝ (Fin 5) → ℝ,CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀,x₀≠0 ∧
        (∀ N : ℕ,c*rate μ L (polyakAlpha μ L) (polyakBeta μ L)^N*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖) ∧
        (∀ N : ℕ,
          c*rate μ L (polyakAlpha μ L) (polyakBeta μ L)^N≤
            worst μ L (polyakAlpha μ L) (polyakBeta μ L) 5 N ∧
          worst μ L (polyakAlpha μ L) (polyakBeta μ L) 5 N≤
            worstAll μ L (polyakAlpha μ L) (polyakBeta μ L) N ∧
          worstAll μ L (polyakAlpha μ L) (polyakBeta μ L) N≤
            C*rate μ L (polyakAlpha μ L) (polyakBeta μ L)^N) := by
  obtain ⟨f,hf,x₀,hx,a,ha,hfbound⟩ := exists_five_dimensional_optimal_example hμ hL
  obtain ⟨b,hb,hlower⟩ := exists_worst_five_optimal_lower hμ hL
  obtain ⟨C,hC,hupper⟩ := FiniteHorizon.exists_original_prefactor hμ hL
  let c := min a b
  have hc : 0<c := lt_min ha hb
  have hnonneg : 0≤rate μ L (polyakAlpha μ L) (polyakBeta μ L) := by
    rw [originalRate_eq_exp_T hμ hL]
    exact (Real.exp_pos _).le
  have hlow (N : ℕ) : c*rate μ L (polyakAlpha μ L) (polyakBeta μ L)^N≤
      worst μ L (polyakAlpha μ L) (polyakBeta μ L) 5 N := by
    calc
      _≤b*rate μ L (polyakAlpha μ L) (polyakBeta μ L)^N :=
        mul_le_mul_of_nonneg_right (min_le_right a b) (pow_nonneg hnonneg N)
      _≤_ := by
        rw [originalRate_eq_exp_T hμ hL,←Real.exp_nat_mul]
        exact hlower N
  have hmid (N : ℕ) : worst μ L (polyakAlpha μ L) (polyakBeta μ L) 5 N≤
      worstAll μ L (polyakAlpha μ L) (polyakBeta μ L) N :=
    worst_le_worstAll hμ hL (polyakAlpha_pos hμ hL).le (polyakBeta_mem hμ hL).1 (by norm_num) N
  have hcC : c≤C := by
    have hh := (hlow 0).trans ((hmid 0).trans (hupper 0))
    simpa only [pow_zero,mul_one] using hh
  refine ⟨c,C,hc,hcC,hC,f,hf,x₀,hx,?_,fun N => ⟨hlow N,hmid N,hupper N⟩⟩
  intro N
  calc
    _≤a*rate μ L (polyakAlpha μ L) (polyakBeta μ L)^N*‖x₀‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left a b) (pow_nonneg hnonneg N)) (norm_nonneg _)
    _≤_ := by
      rw [originalRate_eq_exp_T hμ hL,←Real.exp_nat_mul]
      exact hfbound N

end polyak.Results
