import krylov.LotkaVolterra.GlobalEndpointOrbit
import krylov.Strings.FeedbackAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
Article: main_krylov, thm:value, global optimizer construction from LV time.
Use: construct the physical state and increasing physical clock by quadrature,
without assuming a pre-existing feedback trajectory in physical coordinates.
Source: FTC, exponential differentiation and the scalar inverse function theorem.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- Primitive initialized at zero. -/
def primitive (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, f u

/-- Exponential coordinate initialized at one. -/
def expPrimitive (f : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (primitive f t)

/-- FTC differentiates the continuous orbit-rate primitive. -/
theorem primitive_derivative {f : ℝ → ℝ} (hc : Continuous f) (t : ℝ) :
    HasDerivAt (primitive f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The continuous primitive has the strict derivative needed for local inversion. -/
theorem primitive_strictDerivative {f : ℝ → ℝ} (hc : Continuous f) (t : ℝ) :
    HasStrictDerivAt (primitive f) (f t) t :=
  intervalIntegral.integral_hasStrictDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The exponential primitive solves its scalar linear growth equation. -/
theorem expPrimitive_derivative {f : ℝ → ℝ} (hc : Continuous f) (t : ℝ) :
    HasDerivAt (expPrimitive f) (f t * expPrimitive f t) t := by
  change HasDerivAt (fun u ↦ Real.exp (primitive f u)) (f t * Real.exp (primitive f t)) t
  convert (primitive_derivative hc t).exp using 1
  ring

/-- The exponential primitive of a continuous rate is continuous. -/
theorem expPrimitive_continuous {f : ℝ → ℝ} (hc : Continuous f) : Continuous (expPrimitive f) := by
  exact continuous_iff_continuousAt.mpr (fun t ↦ (expPrimitive_derivative hc t).continuousAt)

/-- Every quadrature primitive vanishes at its initial time. -/
@[simp] theorem primitive_zero (f : ℝ → ℝ) : primitive f 0 = 0 := by simp [primitive]
/-- Every exponential primitive starts at one. -/
@[simp] theorem expPrimitive_zero (f : ℝ → ℝ) : expPrimitive f 0 = 1 := by simp [expPrimitive]

/-- Every exponential quadrature is strictly positive. -/
theorem expPrimitive_pos (f : ℝ → ℝ) (t : ℝ) : 0 < expPrimitive f t := Real.exp_pos _

/-- The quadrature state has the actual LV state ratio, obtained by a proved
conserved quantity. The supplied differential equation is the LV coordinate
equation, not a desired physical feedback identity. -/
theorem coordinate_ratio {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    {t : ℝ} (ht : 0 ≤ t) :
    U t = stateRatio (expPrimitive s t) (Real.exp t) (expPrimitive U t) := by
  let C : ℝ → ℝ := fun u ↦ U u * expPrimitive U u / (expPrimitive s u * Real.exp u)
  have hC : ∀ u > 0, HasDerivAt C 0 u := by
    intro u hu
    have hd := ((hode u hu).mul (expPrimitive_derivative hU u)).div
      ((expPrimitive_derivative hs u).mul (Real.hasDerivAt_exp u))
      (mul_ne_zero (expPrimitive_pos s u).ne' (Real.exp_ne_zero u))
    convert hd using 1
    dsimp
    ring
  have hCc : Continuous C := by
    exact (hU.mul (expPrimitive_continuous hU)).div
      ((expPrimitive_continuous hs).mul Real.continuous_exp)
      (fun u ↦ mul_ne_zero (expPrimitive_pos s u).ne' (Real.exp_ne_zero u))
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hCc.continuousOn
    (f' := fun _ : ℝ ↦ (0 : ℝ)) (fun u hu ↦ hC u hu.1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume 0 t)
  have hCt : C t = 1 := by
    have hC₀ : C 0 = 1 := by simp [C, hU₀]
    simpa only [intervalIntegral.integral_zero, hC₀, sub_eq_zero] using hint.symm
  dsimp [C] at hCt
  dsimp [stateRatio]
  apply (eq_div_iff (expPrimitive_pos U t).ne').mpr
  exact (div_eq_one_iff_eq (mul_ne_zero (expPrimitive_pos s t).ne' (Real.exp_ne_zero t))).mp hCt

/-- Physical length accrued per unit LV time. -/
def physicalSpeed (s : ℝ → ℝ) (t : ℝ) : ℝ := expPrimitive s t * s t / Real.exp t

/-- The physical clock is constructed by integrating its actual speed. -/
def physicalClock (s : ℝ → ℝ) : ℝ → ℝ := primitive (physicalSpeed s)

/-- A continuous control state gives a continuous physical clock speed. -/
theorem physicalSpeed_continuous {s : ℝ → ℝ} (hs : Continuous s) : Continuous (physicalSpeed s) := by
  unfold physicalSpeed
  exact ((expPrimitive_continuous hs).mul hs).div Real.continuous_exp Real.exp_ne_zero

/-- A positive control state gives a positive physical clock speed. -/
theorem physicalSpeed_pos {s : ℝ → ℝ} (hs : ∀ t, 0 < s t) (t : ℝ) :
    0 < physicalSpeed s t := div_pos (mul_pos (expPrimitive_pos s t) (hs t)) (Real.exp_pos t)

/-- The physical clock has the constructed physical speed as its derivative. -/
theorem physicalClock_derivative {s : ℝ → ℝ} (hs : Continuous s) (t : ℝ) :
    HasDerivAt (physicalClock s) (physicalSpeed s t) t :=
  primitive_derivative (physicalSpeed_continuous hs) t

/-- The physical clock has the strict derivative required by the inverse-function theorem. -/
theorem physicalClock_strictDerivative {s : ℝ → ℝ} (hs : Continuous s) (t : ℝ) :
    HasStrictDerivAt (physicalClock s) (physicalSpeed s t) t :=
  primitive_strictDerivative (physicalSpeed_continuous hs) t

/-- Initial LV time corresponds to the physical origin. -/
@[simp] theorem physicalClock_zero (s : ℝ → ℝ) : physicalClock s 0 = 0 := primitive_zero _

/-- Positive physical speed makes the actual physical clock strictly increasing. -/
theorem physicalClock_strictMono {s : ℝ → ℝ} (hs : Continuous s) (hp : ∀ t, 0 < s t) :
    StrictMono (physicalClock s) :=
  strictMono_of_hasDerivAt_pos (physicalClock_derivative hs) (physicalSpeed_pos hp)

/-- The genuine inverse of the physical clock has the correct derivative at
every point in its range; global injectivity identifies the local inverses. -/
theorem inverseClock_derivative {s : ℝ → ℝ} (hs : Continuous s) (hp : ∀ t, 0 < s t) (t : ℝ) :
    HasDerivAt (Function.invFun (physicalClock s)) (physicalSpeed s t)⁻¹ (physicalClock s t) := by
  have hinj := (physicalClock_strictMono hs hp).injective
  exact ((physicalClock_strictDerivative hs t).to_local_left_inverse
    (physicalSpeed_pos hp t).ne'
    (Eventually.of_forall (Function.leftInverse_invFun hinj))).hasDerivAt

/-- A lower bound for the true integrated logarithmic position. -/
theorem primitive_ge_two_mul {s : ℝ → ℝ} (hs : Continuous s)
    (h₂ : ∀ t ≥ 0, 2 ≤ s t) {t : ℝ} (ht : 0 ≤ t) : 2 * t ≤ primitive s t := by
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (2 : ℝ)) volume 0 t)
    (hs.intervalIntegrable 0 t) (fun u hu ↦ h₂ u hu.1)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, primitive] using hi

/-- The physical speed is bounded below, so physical time does not end at a
finite length when the positive LV orbit persists for all LV times. -/
theorem physicalSpeed_ge_two {s : ℝ → ℝ} (hs : Continuous s)
    (h₂ : ∀ t ≥ 0, 2 ≤ s t) {t : ℝ} (ht : 0 ≤ t) : 2 ≤ physicalSpeed s t := by
  have hp := primitive_ge_two_mul hs h₂ ht
  have hexp : Real.exp t ≤ expPrimitive s t := by
    apply Real.exp_le_exp.mpr
    linarith
  apply (le_div_iff₀ (Real.exp_pos t)).mpr
  nlinarith [h₂ t ht, expPrimitive_pos s t]

/-- The constructed physical clock grows at least linearly. -/
theorem physicalClock_ge_two_mul {s : ℝ → ℝ} (hs : Continuous s)
    (h₂ : ∀ t ≥ 0, 2 ≤ s t) {t : ℝ} (ht : 0 ≤ t) : 2 * t ≤ physicalClock s t := by
  exact primitive_ge_two_mul (physicalSpeed_continuous hs)
    (fun u hu ↦ physicalSpeed_ge_two hs h₂ hu) ht

/-- A unit logarithmic-position bound suffices for all physical-clock
constructions, including arbitrarily small positive gamma. -/
theorem primitive_ge_self {s : ℝ → ℝ} (hs : Continuous s)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) {t : ℝ} (ht : 0 ≤ t) : t ≤ primitive s t := by
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 t)
    (hs.intervalIntegrable 0 t) (fun u hu ↦ h₁ u hu.1)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, primitive] using hi

/-- A state at least one gives speed at least one on nonnegative LV time. -/
theorem physicalSpeed_ge_one {s : ℝ → ℝ} (hs : Continuous s)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ physicalSpeed s t := by
  have he : Real.exp t ≤ expPrimitive s t := Real.exp_le_exp.mpr (primitive_ge_self hs h₁ ht)
  apply (le_div_iff₀ (Real.exp_pos t)).mpr
  nlinarith [h₁ t ht, expPrimitive_pos s t]

/-- The physical clock dominates nonnegative LV time. -/
theorem physicalClock_ge_self {s : ℝ → ℝ} (hs : Continuous s)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) {t : ℝ} (ht : 0 ≤ t) : t ≤ physicalClock s t :=
  primitive_ge_self (physicalSpeed_continuous hs)
    (fun _ hu ↦ physicalSpeed_ge_one hs h₁ hu) ht

/-- The lower speed bound makes the actual clock reach arbitrarily large physical lengths. -/
theorem physicalClock_tendsto_atTop {s : ℝ → ℝ} (hs : Continuous s)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) : Tendsto (physicalClock s) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht ↦ physicalClock_ge_self hs h₁ ht))
  exact tendsto_id

/-- Every nonnegative physical position has an actual nonnegative LV time. -/
theorem physicalClock_surjOn {s : ℝ → ℝ} (hs : Continuous s)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) : SurjOn (physicalClock s) (Ici 0) (Ici 0) := by
  have hc : Continuous (physicalClock s) := continuous_iff_continuousAt.mpr
    (fun t ↦ (physicalClock_derivative hs t).continuousAt)
  have hi := intermediate_value_Ici (a := (0 : ℝ)) hc.continuousOn (physicalClock_tendsto_atTop hs h₁)
  intro x hx
  exact hi (by simpa only [physicalClock_zero] using hx)

/-- The canonical inverse is a true right inverse on the entire physical
half-line. This is established by the actual clock range, not postulated. -/
theorem inverseClock_right_inverse {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {x : ℝ} (hx : 0 ≤ x) :
    physicalClock s (Function.invFun (physicalClock s) x) = x := by
  obtain ⟨t, _, ht⟩ := physicalClock_surjOn hs h₁ hx
  rw [← ht, Function.leftInverse_invFun (physicalClock_strictMono hs hp).injective]

/-- The actual inverse physical clock sends the source half-line into nonnegative LV time. -/
theorem inverseClock_nonneg {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Function.invFun (physicalClock s) x := by
  have he := inverseClock_right_inverse hs hp h₁ hx
  apply (physicalClock_strictMono hs hp).le_iff_le.mp
  simpa only [physicalClock_zero, he] using hx

/-- Inverse-clock differentiation holds at every nonnegative physical point. -/
theorem inverseClock_derivative_nonneg {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (Function.invFun (physicalClock s))
      (physicalSpeed s (Function.invFun (physicalClock s) x))⁻¹ x := by
  simpa only [inverseClock_right_inverse hs hp h₁ hx] using
    inverseClock_derivative hs hp (Function.invFun (physicalClock s) x)

/-- Unbounded LV times are really reached along unbounded physical positions. -/
theorem inverseClock_tendsto_atTop {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) :
    Tendsto (Function.invFun (physicalClock s)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  refine eventually_atTop.2 ⟨max (physicalClock s b) 0, ?_⟩
  intro x hx
  have hx₀ : 0 ≤ x := (le_max_right _ _).trans hx
  apply (physicalClock_strictMono hs hp).le_iff_le.mp
  rw [inverseClock_right_inverse hs hp h₁ hx₀]
  exact (le_max_left _ _).trans hx

end
end krylov.Strings.OptimizerQuadratures
