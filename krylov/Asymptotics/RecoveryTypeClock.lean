import krylov.Strings.TypeClockInverse
import krylov.Strings.OptimizerQuadratures
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: main_krylov, thm:limit, lower recovery in the actual type variable.
Use: invert the genuine primitive of a continuous positive physical density.
A slightly larger physical window places both recovery endpoints inside the
clock image, so the inverse derivative is ordinary even at the initial atom.
Source: FTC, the intermediate value theorem, and the proved compact clock
inverse theorem. All clocks and inverses below are actual functions.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Filter
open scoped Topology
open krylov.Strings

/-- A specified continuous derivative gives genuine compact C¹ regularity. -/
theorem contDiffOn_one_of_continuous_derivative {f d : ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hd : ∀ x ∈ s, HasDerivWithinAt f (d x) s x)
    (hc : ContinuousOn d s) : ContDiffOn ℝ 1 f s := by
  rw [contDiffOn_one_iff_derivWithin hs]
  refine ⟨fun x hx ↦ (hd x hx).differentiableWithinAt, ?_⟩
  exact hc.congr (fun x hx ↦ (hd x hx).derivWithin (hs x hx))

/-- The true type clock of the chosen physical density representative. -/
def recoveryTypeClock (v : ℝ → ℝ) : ℝ → ℝ := OptimizerQuadratures.primitive v

/-- The actual inverse type clock used on the finite physical window `[0,X]`.
The larger inverse window makes zero an interior inverse-function point. -/
def recoveryTypeInverse (v : ℝ → ℝ) (X : ℝ) : ℝ → ℝ :=
  TypeChange.inverse (recoveryTypeClock v) (-1) (X + 1)

/-- The physical state pulled back through the genuine type clock. -/
def recoveryTypePullback (v : ℝ → ℝ) (X : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y ↦ f (recoveryTypeInverse v X y)

theorem recoveryTypeClock_derivative {v : ℝ → ℝ} (hc : Continuous v) (x : ℝ) :
    HasDerivAt (recoveryTypeClock v) (v x) x := OptimizerQuadratures.primitive_derivative hc x

theorem recoveryTypeClock_continuous {v : ℝ → ℝ} (hc : Continuous v) :
    Continuous (recoveryTypeClock v) :=
  continuous_iff_continuousAt.mpr (fun x ↦ (recoveryTypeClock_derivative hc x).continuousAt)

@[simp] theorem recoveryTypeClock_zero (v : ℝ → ℝ) : recoveryTypeClock v 0 = 0 := by
  simp [recoveryTypeClock]

theorem recoveryTypeClock_strictMono {v : ℝ → ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) : StrictMono (recoveryTypeClock v) :=
  strictMono_of_hasDerivAt_pos (recoveryTypeClock_derivative hc) hv

theorem recoveryTypeClock_pos {v : ℝ → ℝ} {X : ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) (hX : 0 < X) : 0 < recoveryTypeClock v X := by
  simpa only [recoveryTypeClock_zero] using recoveryTypeClock_strictMono hc hv hX

/-- Every point of the actual recovery type interval is interior to the
larger inverse clock image. -/
theorem recoveryTypeClock_window {v : ℝ → ℝ} {X y : ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) (_hX : 0 < X) (hy : y ∈ Icc 0 (recoveryTypeClock v X)) :
    y ∈ Ioo (recoveryTypeClock v (-1)) (recoveryTypeClock v (X + 1)) := by
  have hm := recoveryTypeClock_strictMono hc hv
  have hl := hm (by norm_num : (-1 : ℝ) < 0)
  have hr := hm (by linarith : X < X + 1)
  simp only [recoveryTypeClock_zero] at hl
  exact ⟨hl.trans_le hy.1, hy.2.trans_lt hr⟩

/-- The inverse has the true nonnegative physical position, bounded by X. -/
theorem recoveryTypeInverse_mem {v : ℝ → ℝ} {X y : ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) (hX : 0 < X) (hy : y ∈ Icc 0 (recoveryTypeClock v X)) :
    recoveryTypeInverse v X y ∈ Icc 0 X := by
  have hw := recoveryTypeClock_window hc hv hX hy
  have he := TypeChange.clock_inverse (by linarith : (-1 : ℝ) ≤ X + 1)
    (recoveryTypeClock_continuous hc).continuousOn ⟨hw.1.le, hw.2.le⟩
  change recoveryTypeClock v (recoveryTypeInverse v X y) = y at he
  have hm := recoveryTypeClock_strictMono hc hv
  constructor
  · exact hm.le_iff_le.mp (by simpa only [recoveryTypeClock_zero, he] using hy.1)
  · exact hm.le_iff_le.mp (by simpa only [he] using hy.2)

/-- Genuine inverse derivative, valid at both endpoints of the recovery interval. -/
theorem recoveryTypeInverse_derivative {v : ℝ → ℝ} {X y : ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) (hX : 0 < X) (hy : y ∈ Icc 0 (recoveryTypeClock v X)) :
    HasDerivAt (recoveryTypeInverse v X) (v (recoveryTypeInverse v X y))⁻¹ y := by
  exact TypeChange.inverse_hasDerivAt (by linarith)
    (recoveryTypeClock_continuous hc).continuousOn
    ((recoveryTypeClock_strictMono hc hv).strictMonoOn _)
    (recoveryTypeClock_window hc hv hX hy) (recoveryTypeClock_derivative hc _)
    (hv _).ne'

/-- Compact C¹ regularity of the actual inverse follows from continuity and
strict positivity of the physical density, with no C¹ assumption on it. -/
theorem recoveryTypeInverse_contDiffOn {v : ℝ → ℝ} {X : ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) (hX : 0 < X) :
    ContDiffOn ℝ 1 (recoveryTypeInverse v X) (Icc 0 (recoveryTypeClock v X)) := by
  have hY := recoveryTypeClock_pos hc hv hX
  have hi : ContinuousOn (recoveryTypeInverse v X) (Icc 0 (recoveryTypeClock v X)) :=
    fun y hy ↦ (recoveryTypeInverse_derivative hc hv hX hy).continuousAt.continuousWithinAt
  apply contDiffOn_one_of_continuous_derivative (uniqueDiffOn_Icc hY)
    (fun y hy ↦ (recoveryTypeInverse_derivative hc hv hX hy).hasDerivWithinAt)
  exact (hc.comp_continuousOn hi).inv₀ (fun y _hy ↦ (hv _).ne')

@[simp] theorem recoveryTypeInverse_zero {v : ℝ → ℝ} {X : ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) (hX : 0 < X) : recoveryTypeInverse v X 0 = 0 := by
  have hh := TypeChange.inverse_clock ((recoveryTypeClock_strictMono hc hv).strictMonoOn _)
    (show (0 : ℝ) ∈ Icc (-1) (X + 1) from ⟨by norm_num, by linarith⟩)
  simpa only [recoveryTypeClock_zero, recoveryTypeInverse] using hh

/-- True C¹ physical functions remain C¹ after the actual type change. -/
theorem recoveryTypePullback_contDiffOn {v f : ℝ → ℝ} {X : ℝ} (hc : Continuous v)
    (hv : ∀ x, 0 < v x) (hX : 0 < X) (hf : ContDiffOn ℝ 1 f (Icc 0 X)) :
    ContDiffOn ℝ 1 (recoveryTypePullback v X f) (Icc 0 (recoveryTypeClock v X)) :=
  hf.comp (recoveryTypeInverse_contDiffOn hc hv hX)
    (fun _y hy ↦ recoveryTypeInverse_mem hc hv hX hy)

end
end krylov.Asymptotics
