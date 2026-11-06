import nesterov.Spectral.Planar
import nesterov.Spectral.Feasibility
import polyak.Waves.Mixture

/-! Actual L² realization of the division-free spectral interpolation table. -/
noncomputable section
open MeasureTheory
namespace nesterov.Spectral
open polyak.Interpolation
abbrev WaveSpace := polyak.Waves.WaveSpace
abbrev lift := polyak.Waves.lift

def positionMap (m : SymbolPair) (t : ℝ) (i : Option ℕ) : C(Frequency, ℂ) :=
  m.u * polyak.Waves.positionMap t i

def gradientMap (m : SymbolPair) (t : ℝ) (i : Option ℕ) : C(Frequency, ℂ) :=
  m.p * polyak.Waves.positionMap t i

def valueMap (m : SymbolPair) (C t : ℝ) (i : Option ℕ) : C(Frequency, ℝ) where
  toFun c := Planar.value (m.u c) (m.p c) C t (Real.arccos c) i
  continuous_toFun := by
    cases i with
    | none => exact continuous_const
    | some k =>
      change Continuous (fun c => (C + 2 * (m.p c * star (m.u c)).re) / 4 *
        Complex.normSq (polyak.Waves.positionMap t (some k) c))
      fun_prop

def mixturePosition (ν : Spectrum) (m : SymbolPair) (t : ℝ) (i : Option ℕ) : WaveSpace ν :=
  lift ν (positionMap m t i)

def mixtureGradient (ν : Spectrum) (m : SymbolPair) (t : ℝ) (i : Option ℕ) : WaveSpace ν :=
  lift ν (gradientMap m t i)

def mixtureValue (ν : Spectrum) (m : SymbolPair) (C t : ℝ) (i : Option ℕ) : ℝ :=
  ∫ c, valueMap m C t i c ∂ν

/-- Article: integration of a signed spectral slack. Proof: real linearity and unit mass. -/
theorem integral_spectral_slack (ν : Spectrum) (m : SymbolPair) (C t δ : ℝ) (n : ℕ) :
    (∫ c, g m c *
        (Real.cosh (n * t) - Real.cos (n * Real.arccos c)) -
      δ * (2 * skew m c * Real.sin (n * Real.arccos c)) +
        δ * C * Real.sinh (n * t) ∂ν) =
    meanA ν m t n - δ * meanB ν m n + δ * C * Real.sinh (n * t) := by
  have ha := polyak.Spectral.integrable_continuous ν (show Continuous (fun c : Frequency =>
      g m c *
        (Real.cosh (n * t) - Real.cos (n * Real.arccos c))) by unfold g; fun_prop)
  have hb := polyak.Spectral.integrable_continuous ν (show Continuous (fun c : Frequency =>
      2 * skew m c * Real.sin (n * Real.arccos c)) by unfold skew; fun_prop)
  have hs := integral_add (ha.sub (hb.const_mul δ))
    (integrable_const (δ * C * Real.sinh (n * t)))
  dsimp only [Pi.sub_apply] at hs
  rw [hs, integral_sub ha (hb.const_mul δ), integral_const_mul]
  simp [meanA, meanB, lagA, lagB]

/-- Article: exact spectral lag formula, both signs at once. Proof: integrate the planar formula. -/
theorem mixture_slack (ν : Spectrum) (m : SymbolPair) (C t δ : ℝ) (j n : ℕ) :
    datumR (mixturePosition ν m t) (mixtureGradient ν m t) (some j) (some (j + n)) +
      δ * datumT (mixturePosition ν m t) (mixtureGradient ν m t) (mixtureValue ν m C t)
        (some j) (some (j + n)) =
      (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
        (meanA ν m t n - δ * meanB ν m n + δ * C * Real.sinh (n * t)) := by
  unfold mixturePosition mixtureGradient mixtureValue
  rw [polyak.Waves.datum_slack_lift ν (positionMap m t) (gradientMap m t) (valueMap m C t) δ]
  calc
    _ = ∫ c, (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
        (g m c *
          (Real.cosh (n * t) - Real.cos (n * Real.arccos c)) -
          δ * (2 * skew m c * Real.sin (n * Real.arccos c)) +
            δ * C * Real.sinh (n * t)) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun c => Planar.datum_slack (m.u c) (m.p c) C t (Real.arccos c) δ j n)
    _ = _ := by rw [integral_const_mul, integral_spectral_slack]

/-- Article: exact spectral minimizer formula, both signs at once. Proof: integrate the origin pair. -/
theorem mixture_star_slack (ν : Spectrum) (m : SymbolPair) (C t δ : ℝ) (j : ℕ) :
    datumR (mixturePosition ν m t) (mixtureGradient ν m t) none (some j) +
      δ * datumT (mixturePosition ν m t) (mixtureGradient ν m t) (mixtureValue ν m C t)
        none (some j) =
      (1 / 4 : ℝ) * Real.exp (2 * j * t) * (meanG ν m + δ * C) := by
  unfold mixturePosition mixtureGradient mixtureValue
  rw [polyak.Waves.datum_slack_lift ν (positionMap m t) (gradientMap m t) (valueMap m C t) δ]
  calc
    _ = ∫ c, (1 / 4 : ℝ) * Real.exp (2 * j * t) *
        (g m c + δ * C) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun c => Planar.datum_star_slack (m.u c) (m.p c) C t (Real.arccos c) δ j)
    _ = _ := by
      rw [integral_const_mul, integral_add (polyak.Spectral.integrable_continuous ν (by unfold g; fun_prop))
        (integrable_const _)]
      simp [meanG]

/-- Article: prescribed common function values in Lemma spectralinterp.
Proof: the squared radial factor is independent of frequency and the spectrum has unit mass. -/
theorem mixtureValue_some (ν : Spectrum) (m : SymbolPair) (C t : ℝ) (k : ℕ) :
    mixtureValue ν m C t (some k) =
      (C + 2 * polyak.Spectral.avg ν (fun c => (m.p c * star (m.u c)).re)) / 4 * Real.exp (2 * k * t) := by
  unfold mixtureValue
  have heq : (fun c : Frequency => valueMap m C t (some k) c) =
      (fun c => (C + 2 * (m.p c * star (m.u c)).re) / 4 * Real.exp (2 * k * t)) := by
    funext c
    change (C + 2 * (m.p c * star (m.u c)).re) / 4 * Complex.normSq (polyak.Waves.z t (Real.arccos c) ^ k) = _
    rw [polyak.Waves.normSq_z_pow]
  have hi : Integrable (fun c : Frequency => (m.p c * star (m.u c)).re) (ν : Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by fun_prop)
  rw [heq, integral_mul_const, integral_div,
    integral_add (integrable_const C) (hi.const_mul 2), integral_const_mul]
  simp [polyak.Spectral.avg]

end nesterov.Spectral
