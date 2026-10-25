import polyak.Levels.Program.Weighting
import Mathlib.MeasureTheory.Measure.Support

/-! Measurable (possibly unbounded) changes of spectral density. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels.Threshold

def interiorCarrier : Set Frequency := {ω | 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi}

theorem measurableSet_interiorCarrier : MeasurableSet interiorCarrier := by
  exact ((isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)).measurableSet

def realWeight (d : Frequency→ℝ) (μ : Measure Frequency) : Measure Frequency :=
  μ.withDensity (fun ω => ENNReal.ofReal (d ω))

theorem realWeight_ac (d : Frequency→ℝ) (μ : Measure Frequency) : realWeight d μ≪μ :=
  withDensity_absolutelyContinuous _ _

theorem realWeight_ac_reverse {d : Frequency→ℝ} (μ : Measure Frequency) (hd : Measurable d)
    (hpos : ∀ᵐω∂μ,0<d ω) : μ≪realWeight d μ := by
  exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hd).aemeasurable
    (hpos.mono fun ω hω => (ENNReal.ofReal_pos.mpr hω).ne')

theorem realWeight_ne_zero {d : Frequency→ℝ} {μ : Measure Frequency} (hd : Measurable d)
    (hpos : ∀ᵐω∂μ,0<d ω) (hne : μ≠0) : realWeight d μ≠0 := by
  intro he
  have hac := realWeight_ac_reverse μ hd hpos
  rw [he,Measure.absolutelyContinuous_zero_iff] at hac
  exact hne hac

theorem integral_realWeight {d : Frequency→ℝ} (hd : Measurable d) (hpos : ∀ω,0≤d ω)
    (μ : Measure Frequency) (f : Frequency→ℝ) :
    (∫ ω,f ω ∂realWeight d μ)=∫ ω,d ω*f ω ∂μ := by
  have he := integral_withDensity_eq_integral_toReal_smul (μ:=μ)
    (f:=fun ω => ENNReal.ofReal (d ω)) (ENNReal.measurable_ofReal.comp hd)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f
  simpa only [realWeight,ENNReal.toReal_ofReal (hpos _),smul_eq_mul] using he

theorem integrable_realWeight_iff {d : Frequency→ℝ} (hd : Measurable d) (hpos : ∀ω,0≤d ω)
    (μ : Measure Frequency) (f : Frequency→ℝ) :
    Integrable f (realWeight d μ) ↔ Integrable (fun ω => d ω*f ω) μ := by
  have he := integrable_withDensity_iff_integrable_smul' (μ:=μ) (E:=ℝ)
    (f:=fun ω => ENNReal.ofReal (d ω)) (g:=f) (ENNReal.measurable_ofReal.comp hd)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
  simpa only [realWeight,ENNReal.toReal_ofReal (hpos _),smul_eq_mul] using he

end polyak.Levels.Threshold
