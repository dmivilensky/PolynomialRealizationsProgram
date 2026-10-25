import polyak.FareyPlateau.FanAnalysis.Orders
import polyak.FareyPlateau.FanAnalysis.SourceMass

/-! Passing from large integer fan orders to the actual two-sided
punctured displacement limit, with no fixed sign assumption. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels Filter MeasureTheory Set
open scoped Topology

theorem tendsto_delta_of_order {X : Type*} {l : Filter X} (P : X→Fan.Data)
    {k : ℕ} (hk : 3≤k) (hPk : ∀ᶠ x in l,(P x).k=k)
    (hL : Tendsto (fun x=>(P x).L) l atTop) :
    Tendsto (fun x=>(P x).delta) l (𝓝[≠] (0:ℝ)) := by
  rw [tendsto_def]
  intro s hs
  obtain ⟨L₀,hL₀⟩ := large_order_small_delta hk hs
  filter_upwards [hPk,hL.eventually (eventually_ge_atTop (L₀:ℤ))] with x hx horder
  exact hL₀ (P x) hx horder

namespace Actual
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem arbitrary_carried_mass_fraction_orders {X : Type*} {l : Filter X}
    (P : X→Fan.Data) (a c : X→Frequency) (μ : X→Measure Frequency) (e : ℝ)
    (hL : Tendsto (fun x=>(P x).L) l atTop)
    (hlabels : ∀ᶠ x in l,(P x).j=j ∧ (P x).k=k ∧
      (a x:ℝ)=(P x).near ∧ (c x:ℝ)=(P x).far)
    (hprog : ∀ᶠ x in l,ProgramSolution
      (Geometry.shiftedCurve q (A.edgeShift-e*(P x).delta^2)) nonzeroLags (μ x))
    (hcar : ∀ᶠ x in l,∀ᵐ ω ∂μ x,ω=a x ∨ ω=c x) :
    Tendsto (fun x=>((μ x) {a x}).toReal/((μ x) univ).toReal) l (𝓝 (((k:ℝ)-1)/k)) :=
  arbitrary_carried_mass_fraction A P a c μ e
    (tendsto_delta_of_order P A.period_ge (hlabels.mono (fun _ h=>h.2.1)) hL) hlabels hprog hcar

end Actual
end polyak.FareyPlateau.FanAnalysis
