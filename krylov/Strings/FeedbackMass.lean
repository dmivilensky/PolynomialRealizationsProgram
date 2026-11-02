import krylov.Strings.FeedbackAlgebra
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: main_krylov, thm:value, shape and total-mass calculation.
Use: derive the auxiliary mass balance from the actual feedback differential
equations, rather than postulating the balance as an orbit property.
Source: product and quotient rules in type time; the half-gamma cancellation
is the algebraic identity printed in the proof of thm:value.
-/

namespace krylov.Strings
noncomputable section

/-- Auxiliary mass coordinate H=(s−1)K/φ² along the feedback orbit. -/
def feedbackMassCoordinate (s K φ : ℝ) : ℝ := (s - 1) * K / φ ^ 2

/-- Exact derivative for every gamma, including gamma=1. No saddle
denominator is divided out in this identity. -/
theorem feedbackMassCoordinate_derivative {s K φ : ℝ → ℝ} {y γ t p : ℝ}
    (hφ : HasDerivAt φ (t * φ y) y)
    (hK : HasDerivAt K (stateRatio (φ y) p (K y) * K y / t) y)
    (hs : HasDerivAt s
      (2 * t * (s y - 1 - γ * stateRatio (φ y) p (K y))) y)
    (hφn : φ y ≠ 0) (hKn : K y ≠ 0) (ht : t ≠ 0) (hts : t ^ 2 = s y) :
    HasDerivAt (fun u ↦ feedbackMassCoordinate (s u) (K u) (φ u))
      (K y * stateRatio (φ y) p (K y) / (φ y ^ 2 * t) *
        ((1 - 2 * γ) * s y - 1)) y := by
  convert ((hs.sub_const 1).mul hK).div (hφ.pow 2) (pow_ne_zero 2 hφn) using 1
  · rfl
  · dsimp [stateRatio]
    field_simp
    rw [← hts]
    ring

/-- At gamma=1/2 the mass increment and the auxiliary coordinate cancel.
This is the differential reason the extremal total mass equals s(0). -/
theorem feedback_half_mass_balance {M s K φ : ℝ → ℝ} {y t p : ℝ}
    (hM : HasDerivAt M (feedbackDensity (φ y) p t) y)
    (hφ : HasDerivAt φ (t * φ y) y)
    (hK : HasDerivAt K (stateRatio (φ y) p (K y) * K y / t) y)
    (hs : HasDerivAt s
      (2 * t * (s y - 1 - (1 / 2 : ℝ) * stateRatio (φ y) p (K y))) y)
    (hφn : φ y ≠ 0) (hKn : K y ≠ 0) (ht : t ≠ 0) (hts : t ^ 2 = s y) :
    HasDerivAt (fun u ↦ M u + feedbackMassCoordinate (s u) (K u) (φ u)) 0 y := by
  convert hM.add (feedbackMassCoordinate_derivative hφ hK hs hφn hKn ht hts) using 1
  dsimp [feedbackDensity, stateRatio]
  field_simp
  ring

/-- A proved zero-derivative mass balance is constant on its connected
open domain. The domain may extend slightly to the left of type zero. -/
theorem feedback_mass_conserved {M s K φ : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hc : IsPreconnected I) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hd : ∀ y ∈ I,
      HasDerivAt (fun u ↦ M u + feedbackMassCoordinate (s u) (K u) (φ u)) 0 y) :
    M b + feedbackMassCoordinate (s b) (K b) (φ b) =
      M a + feedbackMassCoordinate (s a) (K a) (φ a) := by
  exact hI.is_const_of_deriv_eq_zero hc
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hd y hy).deriv) hb ha

/-- Unit initialization turns the conserved quantity into the crossing
coordinate itself, with no numerical approximation. -/
theorem feedback_mass_initial (s : ℝ) :
    1 + feedbackMassCoordinate s 1 1 = s := by
  simp [feedbackMassCoordinate]

/-- Once the terminal auxiliary coordinate tends to zero, the conserved
balance gives the total mass. Proving that terminal decay remains a separate
orbit-asymptotic obligation, not a field of an optimal-string structure. -/
theorem feedback_total_mass_of_terminal_decay {M H : ℝ → ℝ} {s₀ : ℝ}
    (hbalance : ∀ y : ℝ, 0 ≤ y → M y + H y = s₀)
    (hH : Filter.Tendsto H Filter.atTop (nhds 0)) :
    Filter.Tendsto M Filter.atTop (nhds s₀) := by
  have hconst : Filter.Tendsto (fun _ : ℝ ↦ s₀) Filter.atTop (nhds s₀) :=
    tendsto_const_nhds
  have h := hconst.sub hH
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
  linarith [hbalance y hy]

end
end krylov.Strings
