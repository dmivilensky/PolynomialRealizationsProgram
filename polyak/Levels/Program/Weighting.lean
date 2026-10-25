import polyak.Levels.Program.Normalization
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Positive continuous reweighting is an exact bijection on finite measures. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

def reweight (d : C(Frequency,ℝ)) (μ : Measure Frequency) : Measure Frequency :=
  μ.withDensity (fun ω => ENNReal.ofReal (d ω))

instance finite_reweight (d : C(Frequency,ℝ)) (μ : Measure Frequency) [IsFiniteMeasure μ] :
    IsFiniteMeasure (reweight d μ) :=
  isFiniteMeasure_withDensity_ofReal (d.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).2

@[simp] theorem reweight_zero (d : C(Frequency,ℝ)) : reweight d 0=0 := by
  simp [reweight]

theorem integral_reweight (d : C(Frequency,ℝ)) (hd : ∀ω,0≤d ω)
    (μ : Measure Frequency) (f : Frequency → ℝ) :
    (∫ ω,f ω ∂reweight d μ)=∫ ω,d ω*f ω ∂μ := by
  have he := integral_withDensity_eq_integral_toReal_smul (μ:=μ)
    (f:=fun ω => ENNReal.ofReal (d ω))
    (ENNReal.measurable_ofReal.comp d.continuous.measurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f
  simpa only [reweight,ENNReal.toReal_ofReal (hd _),smul_eq_mul] using he

def reciprocalDensity (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω) : C(Frequency,ℝ) :=
  ⟨fun ω => 1/d ω,continuous_const.div d.continuous (fun ω => ne_of_gt (hd ω))⟩

theorem reciprocalDensity_pos (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω) (ω : Frequency) :
    0<reciprocalDensity d hd ω := one_div_pos.mpr (hd ω)

theorem reweight_reciprocal (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω)
    (μ : Measure Frequency) : reweight (reciprocalDensity d hd) (reweight d μ)=μ := by
  unfold reweight
  rw [← withDensity_mul μ
    (f:=fun ω => ENNReal.ofReal (d ω))
    (g:=fun ω => ENNReal.ofReal (reciprocalDensity d hd ω))
    (ENNReal.measurable_ofReal.comp d.continuous.measurable)
    (ENNReal.measurable_ofReal.comp (reciprocalDensity d hd).continuous.measurable)]
  have he : (fun ω => ENNReal.ofReal (d ω))*(fun ω => ENNReal.ofReal (reciprocalDensity d hd ω))=1 := by
    funext ω
    simp only [Pi.mul_apply,Pi.one_apply,reciprocalDensity,ContinuousMap.coe_mk]
    rw [← ENNReal.ofReal_mul (hd ω).le,mul_one_div_cancel (ne_of_gt (hd ω)),ENNReal.ofReal_one]
  rw [he,withDensity_one]

theorem reciprocal_reweight (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω)
    (μ : Measure Frequency) : reweight d (reweight (reciprocalDensity d hd) μ)=μ := by
  have he : reciprocalDensity (reciprocalDensity d hd) (reciprocalDensity_pos d hd)=d := by
    ext ω
    simp [reciprocalDensity]
  simpa only [he] using reweight_reciprocal (reciprocalDensity d hd) (reciprocalDensity_pos d hd) μ

theorem reweight_ne_zero_iff (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω)
    (μ : Measure Frequency) : reweight d μ≠0 ↔ μ≠0 := by
  constructor
  · intro h hz
    exact h (by simp [hz])
  · intro h hz
    have he := reweight_reciprocal d hd μ
    rw [hz,reweight_zero] at he
    exact h he.symm

def positiveReweightEquiv (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω) :
    Measure Frequency ≃ Measure Frequency where
  toFun := reweight d
  invFun := reweight (reciprocalDensity d hd)
  left_inv := reweight_reciprocal d hd
  right_inv := reciprocal_reweight d hd

end polyak.Levels
