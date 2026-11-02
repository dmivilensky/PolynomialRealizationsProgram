import krylov.Strings.WindowMass
import Mathlib.Topology.Order.ProjIcc

/-!
Article: main_krylov, s3:def:string, finite and infinite physical lengths.
Use: represent a compact mass restriction by a genuine global `Mass`. The
extension is zero at negative positions and constant beyond the compact right
endpoint. Thus no bounded total mass at a finite string endpoint is required.
Source: mathlib's order projection, one-sided continuity and Stieltjes measure.
-/

namespace krylov.Strings.LocalMass
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Extend a compact cumulative mass by zero before its distinguished atom
and by its endpoint value after the physical window. -/
def cumulative {L : ℝ≥0} (f : StieltjesFunction (Window L)) (x : ℝ) : ℝ :=
  if x < 0 then 0 else f (projIcc 0 (L : ℝ) L.property x)

/-- The compact extension agrees with the original mass at every point of
its window, including both endpoints and all jumps. -/
theorem cumulative_of_mem {L : ℝ≥0} (f : StieltjesFunction (Window L))
    {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    cumulative f x = f ⟨x, hx⟩ := by
  simp only [cumulative, ite_eq_right (not_lt.mpr hx.1)]
  congr 1
  exact projIcc_of_mem L.property hx

/-- Compact right-continuity and monotonicity give a genuine global
Stieltjes function; no behavior beyond the compact window is assumed. -/
def stieltjes {L : ℝ≥0} (f : StieltjesFunction (Window L))
    (hinit : f ⟨0, ⟨le_rfl, L.property⟩⟩ = 1) : StieltjesFunction ℝ where
  toFun := cumulative f
  mono' := by
    intro x y hxy
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · simp only [cumulative, ite_eq_left hx, ite_eq_left hy, le_refl]
      · simp only [cumulative, ite_eq_left hx, ite_eq_right hy]
        have hle := f.mono (monotone_projIcc L.property (not_lt.mp hy))
        have hzero : f (projIcc 0 (L : ℝ) L.property 0) = 1 := by
          convert hinit using 1
          exact congrArg f (projIcc_left L.property)
        exact zero_le_one.trans (hzero ▸ hle)
    · have hy : ¬y < 0 := not_lt.mpr ((not_lt.mp hx).trans hxy)
      simp only [cumulative, ite_eq_right hx, ite_eq_right hy]
      exact f.mono (monotone_projIcc L.property hxy)
  right_continuous' := by
    intro x
    by_cases hx : x < 0
    · apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hx)] with y hy
        simp only [cumulative, ite_eq_left hy]
      · simp only [cumulative, ite_eq_left hx]
    · have hc : ContinuousWithinAt
          (fun y => f (projIcc 0 (L : ℝ) L.property y)) (Ici x) x :=
        (f.right_continuous (projIcc 0 (L : ℝ) L.property x)).comp
          continuous_projIcc.continuousAt.continuousWithinAt
          (fun _ hy => monotone_projIcc L.property hy)
      apply hc.congr
      · intro y hy
        simp only [cumulative, ite_eq_right (not_lt.mpr ((not_lt.mp hx).trans hy))]
      · simp only [cumulative, ite_eq_right hx]

/-- The actual global mass representing this compact string restriction. -/
def toMass {L : ℝ≥0} (f : StieltjesFunction (Window L))
    (hinit : f ⟨0, ⟨le_rfl, L.property⟩⟩ = 1) : Mass where
  cumulative := stieltjes f hinit
  origin := by
    change cumulative f 0 = 1
    rw [cumulative_of_mem f ⟨le_rfl, L.property⟩]
    exact hinit
  negative := by
    intro x hx
    exact ite_eq_left hx

/-- Agreement of cumulative mass on the complete compact interval. -/
theorem toMass_cumulative {L : ℝ≥0} (f : StieltjesFunction (Window L))
    (hinit : f ⟨0, ⟨le_rfl, L.property⟩⟩ = 1)
    {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    (toMass f hinit).cumulative x = f ⟨x, hx⟩ :=
  cumulative_of_mem f hx

/-- Every compact increment has exactly its original mass. The endpoint
convention retains right-endpoint atoms and excludes the initial unit atom. -/
theorem toMass_measure_Ioc {L : ℝ≥0} (f : StieltjesFunction (Window L))
    (hinit : f ⟨0, ⟨le_rfl, L.property⟩⟩ = 1)
    {a b : ℝ} (ha : a ∈ Icc 0 (L : ℝ)) (hb : b ∈ Icc 0 (L : ℝ)) :
    (toMass f hinit).measure (Ioc a b) = ENNReal.ofReal (f ⟨b, hb⟩ - f ⟨a, ha⟩) := by
  rw [Mass.measure_Ioc, toMass_cumulative f hinit ha, toMass_cumulative f hinit hb]

/-- The compact representation stops acquiring mass after its endpoint.
This is a chosen extension, not a boundedness claim about the original string. -/
theorem toMass_cumulative_after {L : ℝ≥0} (f : StieltjesFunction (Window L))
    (hinit : f ⟨0, ⟨le_rfl, L.property⟩⟩ = 1) {x : ℝ} (hx : (L : ℝ) ≤ x) :
    (toMass f hinit).cumulative x = f ⟨L, ⟨L.property, le_rfl⟩⟩ := by
  change cumulative f x = _
  rw [cumulative, ite_eq_right (not_lt.mpr (L.property.trans hx))]
  congr 1
  exact projIcc_of_right_le L.property hx

/-- Restrict a cumulative mass defined on the source's half-open finite
domain to a compact subwindow. No value or bound at the endpoint ℓ is needed. -/
def restrictFinite {ℓ : ℝ} {L : ℝ≥0} (hL : (L : ℝ) < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ)) : StieltjesFunction (Window L) where
  toFun x := f ⟨x, ⟨x.property.1, x.property.2.trans_lt hL⟩⟩
  mono' := by
    intro x y hxy
    exact f.mono hxy
  right_continuous' := by
    intro x
    let e : Window L → Ico (0 : ℝ) ℓ :=
      fun y => ⟨y, ⟨y.property.1, y.property.2.trans_lt hL⟩⟩
    have he : Continuous e := continuous_subtype_val.subtype_mk _
    exact (f.right_continuous (e x)).comp he.continuousAt.continuousWithinAt
      (fun _ hy => hy)

/-- Compact representative of a possibly unbounded mass on [0,ℓ).
The construction applies even when cumulative mass diverges as x approaches ℓ. -/
def ofFiniteWindow {ℓ : ℝ} {L : ℝ≥0} (hL : (L : ℝ) < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (hinit : f ⟨0, ⟨le_rfl, L.property.trans_lt hL⟩⟩ = 1) : Mass :=
  toMass (restrictFinite hL f) hinit

/-- The finite-endpoint representative preserves every physical mass value
on the chosen compact subwindow, with no global extension assumption on f. -/
theorem ofFiniteWindow_cumulative {ℓ : ℝ} {L : ℝ≥0} (hL : (L : ℝ) < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (hinit : f ⟨0, ⟨le_rfl, L.property.trans_lt hL⟩⟩ = 1)
    {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    (ofFiniteWindow hL f hinit).cumulative x =
      f ⟨x, ⟨hx.1, hx.2.trans_lt hL⟩⟩ :=
  toMass_cumulative (restrictFinite hL f) hinit hx

/-- Every half-open increment below ℓ has its source mass, even when f has
infinitely many atoms or becomes unbounded at its excluded endpoint. -/
theorem ofFiniteWindow_measure_Ioc {ℓ : ℝ} {L : ℝ≥0} (hL : (L : ℝ) < ℓ)
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (hinit : f ⟨0, ⟨le_rfl, L.property.trans_lt hL⟩⟩ = 1)
    {a b : ℝ} (ha : a ∈ Icc 0 (L : ℝ)) (hb : b ∈ Icc 0 (L : ℝ)) :
    (ofFiniteWindow hL f hinit).measure (Ioc a b) =
      ENNReal.ofReal (f ⟨b, ⟨hb.1, hb.2.trans_lt hL⟩⟩ -
        f ⟨a, ⟨ha.1, ha.2.trans_lt hL⟩⟩) :=
  toMass_measure_Ioc (restrictFinite hL f) hinit ha hb

/-- Agreement of cumulative values on a compact window implies agreement
of the actual post-origin measures there, on every measurable set. -/
theorem measure_restrict_eq_of_cumulative_eq (M N : Mass) (L : ℝ≥0)
    (h : ∀ x ∈ Icc 0 (L : ℝ), M.cumulative x = N.cumulative x) :
    M.measure.restrict (Ioc 0 (L : ℝ)) = N.measure.restrict (Ioc 0 (L : ℝ)) := by
  have : IsFiniteMeasure (M.measure.restrict (Ioc 0 (L : ℝ))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact M.measure_Ioc_lt_top 0 L
  apply Measure.ext_of_Ioc
  intro a b _hab
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc]
  by_cases hnonempty : max a 0 < min b (L : ℝ)
  · have hlo : max a 0 ∈ Icc 0 (L : ℝ) :=
      ⟨le_max_right _ _, hnonempty.le.trans (min_le_right _ _)⟩
    have hhi : min b (L : ℝ) ∈ Icc 0 (L : ℝ) :=
      ⟨(le_max_right _ _).trans hnonempty.le, min_le_right _ _⟩
    rw [M.measure_Ioc, N.measure_Ioc, h _ hlo, h _ hhi]
  · simp only [Ioc_eq_empty hnonempty, measure_empty]

/-- Representatives on different compact subwindows of the same finite
string give exactly the same measure on their common earlier window.
This permits arbitrary endpoint blowup without imposing a global bound. -/
theorem ofFiniteWindow_compatible {ℓ : ℝ} {L L' : ℝ≥0}
    (hL : (L : ℝ) < ℓ) (hL' : (L' : ℝ) < ℓ) (hLL' : L ≤ L')
    (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
    (hinit : f ⟨0, ⟨le_rfl, L.property.trans_lt hL⟩⟩ = 1) :
    (ofFiniteWindow hL f hinit).measure.restrict (Ioc 0 (L : ℝ)) =
      (ofFiniteWindow hL' f hinit).measure.restrict (Ioc 0 (L : ℝ)) := by
  apply measure_restrict_eq_of_cumulative_eq
  intro x hx
  rw [ofFiniteWindow_cumulative hL f hinit hx,
    ofFiniteWindow_cumulative hL' f hinit ⟨hx.1, hx.2.trans hLL'⟩]

end
end krylov.Strings.LocalMass
