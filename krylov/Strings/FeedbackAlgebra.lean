import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Article: main_krylov, apC:eq:reduced and the feedback construction in thm:value.
Use: exact coordinate identities for the physical string and its change to type time.
Source: ordinary product/quotient differentiation from mathlib. These identities
do not assume existence of the optimizing orbit or a general string state.
-/

namespace krylov.Strings
noncomputable section

/-- Physical state ratio, unchanged by normalization of the string state. -/
def stateRatio (φ p K : ℝ) : ℝ := φ * p / K

/-- The continuous mass density selected by a positive feedback parameter. -/
def feedbackDensity (φ p t : ℝ) : ℝ := p / (φ * t)

/-- Type-time evolution of the physical state ratio. -/
theorem stateRatio_type_derivative {φ p K : ℝ → ℝ} {y t : ℝ}
    (hφ : HasDerivAt φ (t * φ y) y)
    (hp : HasDerivAt p (p y / t) y)
    (hK : HasDerivAt K (stateRatio (φ y) (p y) (K y) * K y / t) y)
    (hKn : K y ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun v ↦ stateRatio (φ v) (p v) (K v))
      (stateRatio (φ y) (p y) (K y) / t *
        (t ^ 2 + 1 - stateRatio (φ y) (p y) (K y))) y := by
  convert (hφ.mul hp).div hK hKn using 1
  · rfl
  · dsimp [stateRatio]
    field_simp

/-- In physical position time the excess φp−K grows at exactly p²;
the mass-density terms cancel. -/
theorem state_excess_derivative {φ p K : ℝ → ℝ} {x v : ℝ}
    (hφ : HasDerivAt φ (p x) x)
    (hp : HasDerivAt p (v ^ 2 * φ x) x)
    (hK : HasDerivAt K (v ^ 2 * φ x ^ 2) x) :
    HasDerivAt (fun u ↦ φ u * p u - K u) (p x ^ 2) x := by
  convert (hφ.mul hp).sub hK using 1
  ring

/-- A nonzero change of clock sends the physical equations to the
printed type-time equations. The density is not a new independent state. -/
theorem feedback_type_rates (φ p K t : ℝ) (hφ : φ ≠ 0) (hp : p ≠ 0)
    (hK : K ≠ 0) (ht : t ≠ 0) :
    p / feedbackDensity φ p t = t * φ ∧
    feedbackDensity φ p t * φ = p / t ∧
    feedbackDensity φ p t * φ ^ 2 = stateRatio φ p K * K / t := by
  dsimp [feedbackDensity, stateRatio]
  constructor
  · field_simp
  constructor <;> field_simp

/-- Positivity needed for logarithms, the type clock and the square loss. -/
theorem feedbackDensity_pos {φ p t : ℝ} (hφ : 0 < φ) (hp : 0 < p)
    (ht : 0 < t) : 0 < feedbackDensity φ p t := by
  exact div_pos hp (mul_pos hφ ht)

/-- Initial density of a string starting from the prescribed unit state. -/
theorem feedbackDensity_initial (t : ℝ) : feedbackDensity 1 1 t = t⁻¹ := by
  simp [feedbackDensity, one_div]

/-- The closed-loop physical equations are the genuine string equations
with this density, not only a formal evolution of the ratio. -/
theorem feedback_physical_rates (φ p t s : ℝ) (hφ : φ ≠ 0) (ht : t ≠ 0)
    (hs : t ^ 2 = s) :
    feedbackDensity φ p t ^ 2 * φ = p ^ 2 / (φ * s) ∧
    feedbackDensity φ p t ^ 2 * φ ^ 2 = p ^ 2 / s := by
  rw [← hs]
  dsimp [feedbackDensity]
  constructor <;> field_simp

/-- Along feedback, the logarithmic physical coordinates have the claimed
type-time velocities. -/
theorem feedback_log_rates {φ p K : ℝ → ℝ} {y t : ℝ}
    (hφ : HasDerivAt φ (t * φ y) y)
    (hp : HasDerivAt p (p y / t) y)
    (hK : HasDerivAt K (stateRatio (φ y) (p y) (K y) * K y / t) y)
    (hφn : φ y ≠ 0) (hpn : p y ≠ 0) (hKn : K y ≠ 0) :
    HasDerivAt (fun v ↦ Real.log (φ v)) t y ∧
    HasDerivAt (fun v ↦ Real.log (p v)) t⁻¹ y ∧
    HasDerivAt (fun v ↦ Real.log (K v))
      (stateRatio (φ y) (p y) (K y) / t) y := by
  constructor
  · convert hφ.log hφn using 1
    field_simp
  constructor
  · convert hp.log hpn using 1
    field_simp
  · convert hK.log hKn using 1
    field_simp

end
end krylov.Strings
