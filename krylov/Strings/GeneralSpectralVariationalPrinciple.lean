import krylov.Strings.GeneralSpectralWeylVariational
import krylov.Strings.GeneralSpectralTents

/-!
Article: main_krylov, apC:prop:tauber, the physical variational principle.
Use: identify the reciprocal boundary compliance with the attained minimum
of the actual mass-plus-gradient energy among physical pairs of trace one.
A genuine finite-prefix tent proves strict positivity. The minimizer is
the normalized actual Neumann solution, not supplied variational data.
Source: the proved physical weak equation and its Cauchy--Schwarz bound.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set MeasureTheory

/-- An actual unit-trace finite-energy tent makes the physical compliance
strictly positive. No assumption on distant or total mass is needed. -/
theorem boundaryCompliance_pos (S : StringMeasure) (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    0 < boundaryCompliance S t ht := by
  have hn := boundaryCompliance_nonneg S t ht
  have htrial := one_le_compliance_mul_trial S t ht
    (boundaryTent_mem_energyGraph S N hf hphysical 0)
    (boundaryTent_trace S N hf 0)
  apply lt_of_le_of_ne hn
  intro hz
  rw [← hz, zero_mul] at htrial
  exact (by norm_num : ¬(1 : ℝ) ≤ 0) htrial

/-- Real scalar multiplication has the literal quadratic physical energy. -/
theorem parameterEnergy_real_smul (S : StringMeasure) (t c : ℝ)
    (w : EnergyAmbient S.measure) :
    parameterEnergy S t ((c : ℂ) • w) = c ^ 2 * parameterEnergy S t w := by
  change t * ‖(c : ℂ) • w.fst‖ ^ 2 + ‖(c : ℂ) • w.snd‖ ^ 2 =
    c ^ 2 * (t * ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2)
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs]
  ring

/-- The true Neumann mass-and-gradient pair normalized by its real
boundary compliance. Its unit trace will follow from positivity. -/
def normalizedParameterSolution (S : StringMeasure) (t : ℝ) (ht : 0 < t) :
    EnergyAmbient S.measure :=
  (((boundaryCompliance S t ht)⁻¹ : ℝ) : ℂ) •
    parameterEnergySolution S t ht (boundaryVector S)

/-- Normalization stays inside the actual closed physical derivative relation. -/
theorem normalizedParameterSolution_mem (S : StringMeasure) (t : ℝ) (ht : 0 < t) :
    normalizedParameterSolution S t ht ∈ energyGraph S :=
  (energyGraph S).toSubmodule.smul_mem _ (parameterEnergySolution_mem S t ht (boundaryVector S))

/-- The actual normalized weak solution has boundary value one. -/
theorem normalizedParameterSolution_trace (S : StringMeasure) (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    boundaryTrace S (normalizedParameterSolution S t ht).fst = 1 := by
  have hp := boundaryCompliance_pos S N hf hphysical t ht
  change boundaryTrace S ((((boundaryCompliance S t ht)⁻¹ : ℝ) : ℂ) •
    (parameterEnergySolution S t ht (boundaryVector S)).fst) = 1
  rw [map_smul, parameter_solution_trace]
  change (((boundaryCompliance S t ht)⁻¹ : ℝ) : ℂ) * (boundaryCompliance S t ht : ℂ) = 1
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ hp.ne', Complex.ofReal_one]

/-- The energy of the normalized actual solution equals the reciprocal
compliance, so the variational infimum will be attained. -/
theorem normalizedParameterSolution_energy (S : StringMeasure) (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    parameterEnergy S t (normalizedParameterSolution S t ht) =
      (boundaryCompliance S t ht)⁻¹ := by
  have hp := boundaryCompliance_pos S N hf hphysical t ht
  rw [normalizedParameterSolution, parameterEnergy_real_smul, parameter_solution_energy]
  field_simp [hp.ne']

/-- Every actual trace-one physical pair has energy at least reciprocal
compliance, by the genuine weak equation and Hilbert Cauchy--Schwarz. -/
theorem reciprocal_compliance_le_energy (S : StringMeasure) (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t)
    {w : EnergyAmbient S.measure} (hw : w ∈ energyGraph S)
    (htrace : boundaryTrace S w.fst = 1) :
    (boundaryCompliance S t ht)⁻¹ ≤ parameterEnergy S t w := by
  rw [← one_div]
  apply (div_le_iff₀ (boundaryCompliance_pos S N hf hphysical t ht)).mpr
  simpa only [mul_comm] using one_le_compliance_mul_trial S t ht hw htrace

/-- The actual energies over which the printed unit-trace variational
principle takes its infimum. Both mass and gradient are physical coordinates. -/
def unitTraceEnergies (S : StringMeasure) (t : ℝ) : Set ℝ :=
  {E | ∃ w : EnergyAmbient S.measure,
    w ∈ energyGraph S ∧ boundaryTrace S w.fst = 1 ∧ parameterEnergy S t w = E}

/-- Reciprocal compliance is the attained least actual unit-trace energy. -/
theorem reciprocal_compliance_isLeast (S : StringMeasure) (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    IsLeast (unitTraceEnergies S t) (boundaryCompliance S t ht)⁻¹ := by
  constructor
  · exact ⟨normalizedParameterSolution S t ht, normalizedParameterSolution_mem S t ht,
      normalizedParameterSolution_trace S N hf hphysical t ht,
      normalizedParameterSolution_energy S N hf hphysical t ht⟩
  · rintro E ⟨w, hw, htrace, rfl⟩
    exact reciprocal_compliance_le_energy S N hf hphysical t ht hw htrace

/-- The exact physical variational identity used in the source tail proof.
The infimum is achieved by `normalizedParameterSolution`. -/
theorem reciprocal_compliance_eq_sInf (S : StringMeasure) (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    (boundaryCompliance S t ht)⁻¹ = sInf (unitTraceEnergies S t) :=
  (reciprocal_compliance_isLeast S N hf hphysical t ht).csInf_eq.symm

end
end krylov.Strings.GeneralSpectral
