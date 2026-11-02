import krylov.Strings.VolterraState
import krylov.Strings.FeedbackMeasureInvariant
import Mathlib.Topology.Order.ProjIcc

/-!
Article: main_krylov, apC:eq:state and the invariant before apC:eq:reduced.
Use: Construct the actual finite-window state of every Stieltjes string and
prove positivity and the Bellman-domain invariant from the integral equations.
Source: the proved finite-measure Volterra contraction, Bochner Fubini, compact
continuous extension, and positive measure integration. No smoothness of the
mass, finiteness of its atoms, or unproved BV chain rule is assumed.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace Mass

/-- A continuous physical position state is integrable on every finite mass
window, including against the singular part of the mass. -/
theorem position_integrable (M : Mass) {φ : ℝ → ℝ} (hφ : Continuous φ) (x : ℝ) :
    IntegrableOn φ (Ioc 0 x) M.measure :=
  hφ.continuousOn.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Ioc
    Ioc_subset_Icc_self (ne_of_lt (M.measure_Ioc_lt_top 0 x))

/-- General-measure cumulative slopes are positive for a normalized monotone
physical position state. -/
theorem slope_one_le (M : Mass) {φ : ℝ → ℝ} (hφ : Monotone φ) (hφ₀ : φ 0 = 1)
    (x : ℝ) : 1 ≤ integralSlope M.measure φ x := by
  have hi : 0 ≤ ∫ t in Ioc 0 x, φ t ∂M.measure := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    have hp := hφ ht.1.le
    rw [hφ₀] at hp
    linarith
  dsimp [integralSlope]
  linarith

/-- The first-order position integral and the Green-kernel form agree against
the original Stieltjes measure. This is the reverse bridge needed for state
uniqueness; atomic right endpoints are retained in both forms. -/
theorem position_integral_eq_green (M : Mass) (L : ℝ≥0) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (x : Window L) :
    (1 + ∫ t in Ioc 0 (x : ℝ), integralSlope M.measure φ t) =
      1 + (x : ℝ) + ∫ y : Window L, Window.kernel x y * φ y ∂M.windowMeasure L := by
  let f : C(Window L, ℝ) := ⟨fun y ↦ φ y, by fun_prop⟩
  calc
    _ = 1 + ∫ t in Ioc 0 (x : ℝ),
        (1 + ∫ y : Window L, if (y : ℝ) ≤ t then f y else 0 ∂M.windowMeasure L) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp [integralSlope, f]
      rw [M.integral_windowMeasure_cumulative L φ (ht.2.trans x.property.2)]
    _ = _ := by
      simpa only [one_mul, f, ContinuousMap.coe_mk] using
        Window.position_integral_eq_free_green (M.windowMeasure L) 1 1 f x

/-- Actual first-order integral states are unique on a finite window. The
proof transports them to the already constructed unique Volterra fixed point;
positivity and monotonicity are conclusions, not uniqueness assumptions. -/
theorem state_unique_on (M : Mass) (L : ℝ≥0) {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (heφ : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (heψ : ∀ x ∈ Icc 0 (L : ℝ), ψ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure ψ t) :
    EqOn φ ψ (Icc 0 (L : ℝ)) := by
  let f : C(Window L, ℝ) := ⟨fun y ↦ φ y, by fun_prop⟩
  let g : C(Window L, ℝ) := ⟨fun y ↦ ψ y, by fun_prop⟩
  have hf : ∀ x, f x = 1 + 1 * (x : ℝ) +
      ∫ y, Window.kernel x y * f y ∂M.windowMeasure L := by
    intro x
    change φ x = _
    rw [heφ x x.property, M.position_integral_eq_green L hφ x]
    simp only [one_mul]
    rfl
  have hg : ∀ x, g x = 1 + 1 * (x : ℝ) +
      ∫ y, Window.kernel x y * g y ∂M.windowMeasure L := by
    intro x
    change ψ x = _
    rw [heψ x x.property, M.position_integral_eq_green L hψ x]
    simp only [one_mul]
    rfl
  obtain ⟨f₀, _, hu⟩ := Window.existsUnique_volterra_finite (M.windowMeasure L) 1 1
  have hfg : f = g := (hu f hf).trans (hu g hg).symm
  intro x hx
  exact congrArg (fun h : C(Window L, ℝ) ↦ h ⟨x, hx⟩) hfg

/-- States constructed on different windows agree throughout their overlap.
This supplies the compatibility needed to patch finite-window constructions. -/
theorem state_overlap (M : Mass) (L₁ L₂ : ℝ≥0) {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (heφ : ∀ x ∈ Icc 0 (L₁ : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (heψ : ∀ x ∈ Icc 0 (L₂ : ℝ), ψ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure ψ t) :
    EqOn φ ψ (Icc 0 ((min L₁ L₂ : ℝ≥0) : ℝ)) := by
  apply M.state_unique_on (min L₁ L₂) hφ hψ
  · intro x hx
    exact heφ x ⟨hx.1, hx.2.trans (show ((min L₁ L₂ : ℝ≥0) : ℝ) ≤ (L₁ : ℝ) by simp)⟩
  · intro x hx
    exact heψ x ⟨hx.1, hx.2.trans (show ((min L₁ L₂ : ℝ≥0) : ℝ) ≤ (L₂ : ℝ) by simp)⟩

/-- Actual state existence on every finite window, including all singular
masses. `p` and `K` are the printed mass integrals, and the position equation
is proved from the Volterra construction by Fubini. The global extension of
`φ` only facilitates notation; its state equation is asserted on the window.
-/
theorem exists_state_on (M : Mass) (L : ℝ≥0) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ φ 0 = 1 ∧ Monotone φ ∧
      ∀ x ∈ Icc 0 (L : ℝ),
        φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t ∧
        1 + x ≤ φ x ∧ 1 ≤ integralSlope M.measure φ x ∧
        1 ≤ integralEnergy M.measure φ x ∧
        1 ≤ stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x) := by
  obtain ⟨f, ⟨hf, hfree, hm⟩, _⟩ := M.existsUnique_displacement L
  let φ : ℝ → ℝ := IccExtend L.property f
  have hc : Continuous φ := f.continuous.Icc_extend'
  have hmφ : Monotone φ := hm.IccExtend L.property
  have hφval (y : Window L) : φ (y : ℝ) = f y := by
    exact congrArg f (projIcc_val L.property y)
  have horigin : φ 0 = 1 := by
    rw [hφval ⟨0, ⟨le_rfl, L.property⟩⟩]
    exact Window.volterra_origin (M.windowMeasure L) 1 1 (by simpa using hf)
  have hcumulative {t : ℝ} (ht : t ≤ L) :
      (∫ y : Window L, if (y : ℝ) ≤ t then f y else 0 ∂M.windowMeasure L) =
        ∫ y in Ioc 0 t, φ y ∂M.measure := by
    calc
      _ = ∫ y : Window L, if (y : ℝ) ≤ t then φ y else 0 ∂M.windowMeasure L := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hφval]
      _ = _ := M.integral_windowMeasure_cumulative L φ ht
  refine ⟨φ, hc, horigin, hmφ, ?_⟩
  intro x hx
  have hval : φ x = f ⟨x, hx⟩ := hφval ⟨x, hx⟩
  have hpos := Window.volterra_position_integral (M.windowMeasure L) 1 1
    (by simpa using hf) ⟨x, hx⟩
  refine ⟨?_, ?_, M.slope_one_le hmφ horigin x, integralEnergy_one_le _ _ _, ?_⟩
  · rw [hval, hpos]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp [integralSlope]
    rw [hcumulative (ht.2.trans hx.2)]
  · rw [hval]
    exact hfree ⟨x, hx⟩
  · exact integral_state_ratio_ge_one hx.1 (le_of_eq horigin.symm) (hmφ.monotoneOn _)
      (M.position_integrable hc x) (M.position_integrable (hc.pow 2) x)

end Mass
end
end krylov.Strings
