import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
Article: main_krylov, s3:def:string and apC:eq:state.
Use: The actual Stieltjes mass of a string, including its distinguished left atom.
Source: mathlib's `StieltjesFunction.measure`, `measure_Ioc`, and
`measure_singleton`. No absolute continuity or absence of atoms is imposed.

This representation has finite cumulative values at every real position.
Finite strings, including mass diverging at their excluded endpoint, are
represented by compatible extensions of compact restrictions in
`krylov.Strings.LocalMass`. No endpoint bound is needed for that construction.
The extension to negative positions records `M(0-) = 0`.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A cumulative mass with finite values on the whole half-line, extended
by zero to negative positions; finite-endpoint strings use compact representatives.
Article: main_krylov, s3:def:string.
Use: Bundle monotonicity, right continuity, and the unit left mass.
-/
structure Mass where
  cumulative : StieltjesFunction ℝ
  origin : cumulative 0 = 1
  negative : ∀ x < 0, cumulative x = 0

namespace Mass

/-- The actual positive Borel measure of the string, including its left atom.
Article: main_krylov, s3:def:string.
Use: Integrate the state and its energy against genuine, possibly singular mass.
-/
def measure (M : Mass) : Measure ℝ := M.cumulative.measure

/-- On the physical half-line the cumulative mass is at least one.
Article: main_krylov, s3:def:string.
Use: Recover the stated codomain from monotonicity and the origin convention.
-/
theorem one_le (M : Mass) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ M.cumulative x := by
  simpa only [M.origin] using M.cumulative.mono hx

/-- The origin's left limit is zero, including for strings with additional atoms.
Article: main_krylov, s3:def:string.
Use: Identify the distinguished left atom through the Stieltjes API.
-/
theorem leftLim_origin (M : Mass) : Function.leftLim M.cumulative 0 = 0 := by
  apply leftLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (M.negative x hx).symm

/-- The left endpoint has exactly unit mass, rather than a separately postulated
normalization unrelated to the measure.
Article: main_krylov, s3:def:string.
Use: Normalize the initial state of the string equation.
-/
@[simp] theorem measure_origin (M : Mass) : M.measure {0} = 1 := by
  simp [measure, M.origin, M.leftLim_origin]

/-- A positive-position atom is exactly the jump of the cumulative mass.
Article: main_krylov, apC:eq:state and apC:lem:fund.
Use: Connect impulse transfers to atoms of the actual Stieltjes measure.
-/
theorem measure_atom (M : Mass) (x : ℝ) :
    M.measure {x} = ENNReal.ofReal (M.cumulative x - Function.leftLim M.cumulative x) :=
  M.cumulative.measure_singleton x

/-- The half-open convention excludes the distinguished initial mass.
Article: main_krylov, apC:eq:state.
Use: Interpret the state integrals on `(0,x]` exactly as printed.
-/
@[simp] theorem measure_Ioc (M : Mass) (a b : ℝ) :
    M.measure (Ioc a b) = ENNReal.ofReal (M.cumulative b - M.cumulative a) :=
  M.cumulative.measure_Ioc a b

/-- Every finite window has finite mass, even when it contains infinitely many
atoms or singular continuous mass.
Article: main_krylov, apC:eq:state.
Use: Supply local finiteness for integration and local existence arguments.
-/
theorem measure_Ioc_lt_top (M : Mass) (a b : ℝ) : M.measure (Ioc a b) < ∞ := by
  rw [M.measure_Ioc]
  exact ENNReal.ofReal_lt_top

/-- The exact mass of a closed physical window includes the unit origin atom.
Article: main_krylov, s3:def:string.
Use: Relate finite-window integration bounds to the cumulative mass.
-/
@[simp] theorem measure_Icc_zero (M : Mass) (x : ℝ) :
    M.measure (Icc 0 x) = ENNReal.ofReal (M.cumulative x) := by
  simp [measure, M.leftLim_origin]

/-- Restriction to a finite physical window is a finite measure.
Article: main_krylov, apC:eq:state.
Use: Permit ordinary Bochner integration on every compact subwindow.
-/
instance finite_restrict (M : Mass) (x : ℝ) : IsFiniteMeasure (M.measure.restrict (Icc 0 x)) := by
  constructor
  simp

/-- The exact real-valued mass acquired after the left endpoint.
Article: main_krylov, apC:eq:state.
Use: Turn Stieltjes mass bounds into real integration estimates.
-/
theorem real_mass_Ioc_zero (M : Mass) {x : ℝ} (hx : 0 ≤ x) :
    (M.measure (Ioc 0 x)).toReal = M.cumulative x - 1 := by
  rw [M.measure_Ioc, M.origin, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (M.one_le hx)

end Mass
end
end krylov.Strings
