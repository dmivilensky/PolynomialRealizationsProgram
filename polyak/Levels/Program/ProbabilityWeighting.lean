import polyak.Levels.Program.Weighting

/-! Normalized positive weighting is a genuine bijection of probability measures. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

def finiteReweight (d : C(Frequency,ℝ)) (μ : FiniteMeasure Frequency) : FiniteMeasure Frequency :=
  ⟨reweight d μ,inferInstance⟩

theorem finiteReweight_smul (d : C(Frequency,ℝ)) (c : NNReal) (μ : FiniteMeasure Frequency) :
    finiteReweight d (c•μ)=c•finiteReweight d μ := by
  apply FiniteMeasure.toMeasure_injective
  change reweight d ((c:ENNReal)•(μ:Measure Frequency))=(c:ENNReal)•reweight d μ
  exact withDensity_smul_measure _ _

theorem finiteReweight_reciprocal (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω) (μ : FiniteMeasure Frequency) :
    finiteReweight (reciprocalDensity d hd) (finiteReweight d μ)=μ := by
  apply FiniteMeasure.toMeasure_injective
  exact reweight_reciprocal d hd μ

theorem finiteReweight_ne_zero (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω)
    {μ : FiniteMeasure Frequency} (hμ : μ≠0) : finiteReweight d μ≠0 := by
  intro he
  have hz := congrArg FiniteMeasure.toMeasure he
  have hne : (μ:Measure Frequency)≠0 := by
    intro hz'
    exact hμ (FiniteMeasure.toMeasure_injective hz')
  exact (reweight_ne_zero_iff d hd μ).mpr hne hz

theorem finiteMeasure_normalize_smul (μ : FiniteMeasure Frequency) (hμ : μ≠0)
    {c : NNReal} (hc : c≠0) : (c•μ).normalize=μ.normalize := by
  have hm : μ.mass≠0 := μ.mass_nonzero_iff.mpr hμ
  have hmass : (c•μ).mass=c*μ.mass := by simp only [FiniteMeasure.mass,FiniteMeasure.smul_apply,smul_eq_mul]
  have hsm : c•μ≠0 := by
    apply (c•μ).mass_nonzero_iff.mp
    rw [hmass]
    exact mul_ne_zero hc hm
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro S _
  rw [(c•μ).normalize_eq_of_nonzero hsm,μ.normalize_eq_of_nonzero hμ,hmass,FiniteMeasure.smul_apply]
  simp only [smul_eq_mul]
  field_simp

def probabilityReweight (d : C(Frequency,ℝ)) (ν : ProbabilityMeasure Frequency) : ProbabilityMeasure Frequency :=
  (finiteReweight d ν.toFiniteMeasure).normalize

theorem probabilityReweight_inverse (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω)
    (ν : ProbabilityMeasure Frequency) :
    probabilityReweight (reciprocalDensity d hd) (probabilityReweight d ν)=ν := by
  let w := finiteReweight d ν.toFiniteMeasure
  have hw : w≠0 := finiteReweight_ne_zero d hd ν.toFiniteMeasure_nonzero
  have hm : w.mass⁻¹≠0 := inv_ne_zero (w.mass_nonzero_iff.mpr hw)
  change (finiteReweight (reciprocalDensity d hd) w.normalize.toFiniteMeasure).normalize=ν
  rw [w.normalize_eq_inv_mass_smul_of_nonzero hw,finiteReweight_smul]
  change (w.mass⁻¹•finiteReweight (reciprocalDensity d hd) (finiteReweight d ν.toFiniteMeasure)).normalize=ν
  rw [finiteReweight_reciprocal,finiteMeasure_normalize_smul ν.toFiniteMeasure ν.toFiniteMeasure_nonzero hm,
    ProbabilityMeasure.toFiniteMeasure_normalize_eq_self]

def probabilityReweightEquiv (d : C(Frequency,ℝ)) (hd : ∀ω,0<d ω) :
    ProbabilityMeasure Frequency ≃ ProbabilityMeasure Frequency where
  toFun := probabilityReweight d
  invFun := probabilityReweight (reciprocalDensity d hd)
  left_inv := probabilityReweight_inverse d hd
  right_inv ν := by
    have he : reciprocalDensity (reciprocalDensity d hd) (reciprocalDensity_pos d hd)=d := by
      ext ω
      simp [reciprocalDensity]
    simpa only [he] using probabilityReweight_inverse (reciprocalDensity d hd) (reciprocalDensity_pos d hd) ν

end polyak.Levels
