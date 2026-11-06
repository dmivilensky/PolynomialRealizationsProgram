import nesterov.Corner.HalfStepConeClassification
import polyak.Spectral.Coordinates

/-! The literal integral cone in the conclusions, including its rational
Dirac rays and the obstruction to a spectrum concentrated in a rational gap.
All measures used in the cone operations are finite. -/
namespace nesterov.Corner
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal

abbrev ConeAngle := polyak.Spectral.Angle

def HalfStepCone (ν : Measure ConeAngle) : Prop :=
  ∀ n : ℕ,1≤n →
    0≤∫ ω,halfStepUpper ω n ∂ν ∧ 0≤∫ ω,halfStepLower ω n ∂ν

theorem continuous_halfStepUpper (n : ℕ) :
    Continuous (fun ω : ConeAngle=>halfStepUpper ω n) := by
  unfold halfStepUpper
  fun_prop

theorem continuous_halfStepLower (n : ℕ) :
    Continuous (fun ω : ConeAngle=>halfStepLower ω n) := by
  unfold halfStepLower
  fun_prop

theorem halfStepCone_zero : HalfStepCone (0 : Measure ConeAngle) := by
  simp [HalfStepCone]

theorem halfStepCone_add {ν η : Measure ConeAngle} [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (hν : HalfStepCone ν) (hη : HalfStepCone η) : HalfStepCone (ν+η) := by
  intro n hn
  have hu (μ : Measure ConeAngle) [IsFiniteMeasure μ] :
      Integrable (fun ω : ConeAngle=>halfStepUpper ω n) μ :=
    (continuous_halfStepUpper n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl (μ : Measure ConeAngle) [IsFiniteMeasure μ] :
      Integrable (fun ω : ConeAngle=>halfStepLower ω n) μ :=
    (continuous_halfStepLower n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  constructor
  · rw [integral_add_measure (hu ν) (hu η)]
    exact add_nonneg (hν n hn).1 (hη n hn).1
  · rw [integral_add_measure (hl ν) (hl η)]
    exact add_nonneg (hν n hn).2 (hη n hn).2

theorem halfStepCone_smul {ν : Measure ConeAngle} (c : ℝ≥0) (hν : HalfStepCone ν) :
    HalfStepCone (c • ν) := by
  intro n hn
  simp only [integral_smul_nnreal_measure]
  exact ⟨mul_nonneg c.coe_nonneg (hν n hn).1,mul_nonneg c.coe_nonneg (hν n hn).2⟩

theorem halfStepCone_dirac_iff (ω : ConeAngle) (hω : 0<(ω:ℝ)) :
    HalfStepCone (Measure.dirac ω) ↔ ∃ K : ℕ,2≤K ∧ (ω:ℝ)=2*Real.pi/K := by
  simp only [HalfStepCone,integral_dirac]
  exact halfStep_positive_lags_iff hω ω.property.2

theorem halfStepCone_canonical (ω : ConeAngle) {K : ℕ} (hK : 2≤K)
    (hω : (ω:ℝ)=2*Real.pi/K) : HalfStepCone (Measure.dirac ω) := by
  intro n _
  simp only [integral_dirac,hω]
  exact ⟨halfStepUpper_atom hK n,halfStepLower_atom hK n⟩

theorem not_halfStepCone_of_gap (ν : ProbabilityMeasure ConeAngle) {K : ℕ} (hK : 2≤K)
    (hgap : ∀ᵐ (ω : ConeAngle) ∂(ν:Measure ConeAngle),
      2*Real.pi/((K:ℝ)+1)<(ω:ℝ) ∧ (ω:ℝ)<2*Real.pi/K) :
    ¬HalfStepCone (ν:Measure ConeAngle) := by
  let f : ConeAngle→ℝ := fun ω=> -halfStepUpper ω K
  have hp : ∀ᵐ (ω : ConeAngle) ∂(ν:Measure ConeAngle),0<f ω :=
    hgap.mono fun _ h=>neg_pos.mpr (halfStepUpper_gap_negative hK h.1 h.2)
  have hi : Integrable f (ν:Measure ConeAngle) :=
    (continuous_halfStepUpper K).neg.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : Function.support f =ᵐ[(ν:Measure ConeAngle)] Set.univ := by
    filter_upwards [hp] with ω hω
    exact propext (iff_true_intro hω.ne')
  have hm : (ν:Measure ConeAngle) (Function.support f)=1 := by
    rw [measure_congr hs,measure_univ]
  have hpos := (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h=>h.le) hi).mpr
    (show 0<(ν:Measure ConeAngle) (Function.support f) by rw [hm];norm_num)
  change 0<∫ ω,-halfStepUpper ω K ∂(ν:Measure ConeAngle) at hpos
  rw [integral_neg] at hpos
  intro hc
  have hh := (hc K (by omega)).1
  linarith

end
end nesterov.Corner
