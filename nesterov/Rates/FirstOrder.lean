import nesterov.Rates.Squared

/-! A normalized first-order rate limit implies the factor tends to one, so
the squared-distance coefficient is twice the distance coefficient. -/
namespace nesterov.Rates
noncomputable section
open Filter
open scoped Topology

theorem factor_tendsto_one {ι : Type*} {l : Filter ι}
    {ρ ε : ι → ℝ} {c : ℝ} (hε : Tendsto ε l (𝓝 0))
    (hne : ∀ᶠ i in l, ε i ≠ 0)
    (hc : Tendsto (fun i => (1-ρ i)/ε i) l (𝓝 c)) :
    Tendsto ρ l (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1:ℝ)) (f := l)).sub (hc.mul hε)
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [hne] with i hi
  field_simp
  ring

theorem squared_coefficient_tendsto {ι : Type*} {l : Filter ι}
    {ρ ε : ι → ℝ} {c : ℝ} (hε : Tendsto ε l (𝓝 0))
    (hne : ∀ᶠ i in l, ε i ≠ 0)
    (hc : Tendsto (fun i => (1-ρ i)/ε i) l (𝓝 c)) :
    Tendsto (fun i => (1-(ρ i)^2)/ε i) l (𝓝 (2*c)) :=
  squared_first_order_constant (factor_tendsto_one hε hne hc) hc

end
end nesterov.Rates
