import polyak.ModeLocking.Plateaus.Definitions
import Mathlib.Analysis.Analytic.Uniqueness

/-! Connected components propagate the locally fixed finite labels.
The analytic identity principle propagates a local determinant equation
through the entire connected projected plateau. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open Set Filter
open scoped Topology

/-- A label on the regular subtype has one value throughout each actual
ambient connected component. No connectedness of the ambient regular set
is assumed. -/
theorem label_constant_on_component {X A : Type*} [TopologicalSpace X] {R : Set X}
    {f : R→A} (hf : IsLocallyConstant f) (x y : R)
    (hy : y.val∈connectedComponentIn R x.val) : f y=f x := by
  rw [connectedComponentIn_eq_image x.property] at hy
  obtain ⟨z,hz,heq⟩ := hy
  have hzy : z=y := Subtype.ext heq
  subst z
  exact hf.apply_eq_of_isPreconnected isPreconnected_connectedComponent hz mem_connectedComponent

/-- Components of the regular boundary are relatively open because the
actual boundary has already been proved locally connected. -/
theorem component_open {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {R : Set X} (hR : IsOpen R) (x : X) : IsOpen (connectedComponentIn R x) :=
  hR.connectedComponentIn

theorem component_connected {X : Type*} [TopologicalSpace X] {R : Set X}
    {x : X} (hx : x∈R) : IsConnected (connectedComponentIn R x) :=
  isConnected_connectedComponentIn_iff.mpr hx

/-- The projection of a connected plateau is connected. With an open
projection map, its parameter domain is open as well. -/
theorem projected_component_open_connected {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [LocallyConnectedSpace X]
    {R : Set X} (hR : IsOpen R) {x : X} (hx : x∈R)
    (p : X→Y) (hp : Continuous p) (hop : IsOpenMap p) :
    IsOpen (p '' connectedComponentIn R x) ∧ IsConnected (p '' connectedComponentIn R x) :=
  ⟨hop _ (component_open hR x),(component_connected hx).image p hp.continuousOn⟩

/-- The determinant at zero shift is an analytic equation on the entire
projected connected component once it holds in the local regular chart. -/
theorem analytic_equation_on_component {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set E} (hU : IsPreconnected U)
    {f : E→ℝ} (hf : AnalyticOnNhd ℝ f U) {x : E} (hx : x∈U)
    (hlocal : f=ᶠ[𝓝 x] 0) : ∀y∈U,f y=0 :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hx hlocal

end polyak.ModeLocking.Plateaus
