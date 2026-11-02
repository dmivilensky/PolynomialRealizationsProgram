import krylov.Strings.GeneralSpectralEnergy
import krylov.Strings.SpectralOperatorCalculus

/-!
Article: main_krylov, apC:prop:tauber, physical resolvents at positive energy.
Use: derive every positive-parameter Neumann resolvent from the constructed
unit resolvent by its genuine continuous functional calculus. The resulting
mass and gradient pair satisfies the actual parameter-dependent weak equation.
Source: the resolvent identity and the multiplicative CFC homomorphism.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set MeasureTheory
open scoped Topology ContinuousFunctionalCalculus

variable (S : StringMeasure)

/-- The actual unit resolvent has spectrum in the physical interval [0,1]. -/
theorem neumannResolvent_spectrum_bounds {r : ℝ} (hr : r ∈ spectrum ℝ (neumannResolvent S)) :
    0 ≤ r ∧ r ≤ 1 := by
  have hn : |r| ≤ 1 := (spectrum.norm_le_norm_of_mem hr).trans (neumannResolvent_norm_le S)
  have hm : 1 - r ∈ spectrum ℝ (1 - neumannResolvent S) := by
    have he : 1 - r ∈ spectrum ℝ
        (algebraMap ℝ (MassHilbert S.measure →L[ℂ] MassHilbert S.measure) 1 - neumannResolvent S) := by
      rw [← spectrum.singleton_sub_eq]
      exact ⟨1, mem_singleton 1, r, hr, rfl⟩
    simpa only [map_one] using he
  have hc : |1 - r| ≤ 1 := (spectrum.norm_le_norm_of_mem hm).trans
    (neumannResolvent_complement_norm_le S)
  exact ⟨by linarith [(le_abs_self (1 - r)).trans hc], (le_abs_self r).trans hn⟩

/-- The positive-parameter resolvent denominator never vanishes on the
actual spectrum; this uses both genuine contraction bounds. -/
theorem resolventDenominator_pos {t : ℝ} (ht : 0 < t)
    (r : spectrum ℝ (neumannResolvent S)) : 0 < 1 + (t - 1) * (r : ℝ) := by
  obtain ⟨h0, h1⟩ := neumannResolvent_spectrum_bounds S r.property
  by_cases h : 1 ≤ t
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) h0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (sub_nonneg.mpr h1)]

/-- The true scalar spectral function of the parameter-t mass resolvent. -/
def resolventFunction (t : ℝ) (ht : 0 < t) : C(spectrum ℝ (neumannResolvent S), ℝ) :=
  ⟨fun r ↦ (r : ℝ) / (1 + (t - 1) * (r : ℝ)),
    continuous_subtype_val.div (by fun_prop) (fun r ↦ (resolventDenominator_pos S ht r).ne')⟩

/-- The actual spectral multiplier converting the unit weak solution to
the parameter-t weak solution. -/
def multiplierFunction (t : ℝ) (ht : 0 < t) : C(spectrum ℝ (neumannResolvent S), ℝ) :=
  ⟨fun r ↦ 1 / (1 + (t - 1) * (r : ℝ)),
    continuous_const.div (by fun_prop) (fun r ↦ (resolventDenominator_pos S ht r).ne')⟩

/-- The genuine parameter-dependent resolvent from actual CFC. -/
def parameterResolvent (t : ℝ) (ht : 0 < t) : MassHilbert S.measure →L[ℂ] MassHilbert S.measure :=
  Spectral.operatorCalculus (neumannResolvent S) (neumannResolvent_selfAdjoint S) (resolventFunction S t ht)

/-- Its genuine CFC source multiplier. -/
def parameterMultiplier (t : ℝ) (ht : 0 < t) : MassHilbert S.measure →L[ℂ] MassHilbert S.measure :=
  Spectral.operatorCalculus (neumannResolvent S) (neumannResolvent_selfAdjoint S) (multiplierFunction S t ht)

/-- The CFC multiplier obeys the true resolvent identity. -/
theorem resolvent_mul_multiplier (t : ℝ) (ht : 0 < t) :
    neumannResolvent S * parameterMultiplier S t ht = parameterResolvent S t ht := by
  rw [parameterMultiplier, parameterResolvent]
  conv_lhs => lhs; rw [← Spectral.operatorCalculus_id (neumannResolvent S) (neumannResolvent_selfAdjoint S)]
  erw [← map_mul]
  congr 1
  ext r
  change (r : ℝ) * (1 / (1 + (t - 1) * (r : ℝ))) = (r : ℝ) / (1 + (t - 1) * (r : ℝ))
  ring

/-- The actual source multiplier is identity plus (1-t) times the actual
parameter resolvent. This is proved on the actual spectrum. -/
theorem multiplier_resolvent_identity (t : ℝ) (ht : 0 < t) :
    parameterMultiplier S t ht = 1 + (1 - t) • parameterResolvent S t ht := by
  have he : multiplierFunction S t ht = 1 + (1 - t) • resolventFunction S t ht := by
    ext r
    change 1 / (1 + (t - 1) * (r : ℝ)) = 1 + (1 - t) * ((r : ℝ) / (1 + (t - 1) * (r : ℝ)))
    field_simp [(resolventDenominator_pos S ht r).ne']
    ring
  rw [parameterMultiplier, he]
  erw [map_add, map_one, map_smul]
  rfl

/-- The actual parameter-t mass and physical-gradient solution. -/
def parameterEnergySolution (t : ℝ) (ht : 0 < t) : MassHilbert S.measure →L[ℂ] EnergyAmbient S.measure :=
  neumannEnergySolution S ∘L parameterMultiplier S t ht

/-- Positive-parameter energy solutions belong to the same actual physical
derivative graph; the parameter changes the energy, not admissible functions. -/
theorem parameterEnergySolution_mem (t : ℝ) (ht : 0 < t) (f : MassHilbert S.measure) :
    parameterEnergySolution S t ht f ∈ energyGraph S :=
  neumannEnergySolution_mem S _

/-- Its actual mass coordinate equals the true CFC parameter resolvent. -/
theorem parameterEnergySolution_fst (t : ℝ) (ht : 0 < t) (f : MassHilbert S.measure) :
    (parameterEnergySolution S t ht f).fst = parameterResolvent S t ht f := by
  change (neumannResolvent S * parameterMultiplier S t ht) f = _
  rw [resolvent_mul_multiplier]

/-- The genuine positive-parameter Neumann weak equation, without a finite
total-mass or compact-resolvent assumption. -/
theorem parameterEnergySolution_variational (t : ℝ) (ht : 0 < t) (f : MassHilbert S.measure)
    {w : EnergyAmbient S.measure} (hw : w ∈ energyGraph S) :
    (t : ℂ) * inner ℂ (parameterResolvent S t ht f) w.fst +
      inner ℂ (parameterEnergySolution S t ht f).snd w.snd = inner ℂ f w.fst := by
  have h := neumannEnergySolution_variational S (parameterMultiplier S t ht f) hw
  have hm : parameterMultiplier S t ht f = f + (1 - t) • parameterResolvent S t ht f := by
    rw [multiplier_resolvent_identity]
    rfl
  have hr : neumannResolvent S (parameterMultiplier S t ht f) = parameterResolvent S t ht f := by
    change (neumannResolvent S * parameterMultiplier S t ht) f = _
    rw [resolvent_mul_multiplier]
  have hh := h
  rw [hr] at hh
  conv_rhs at hh => lhs; rw [hm]
  rw [inner_add_left] at hh
  have hsm : inner ℂ ((1 - t) • parameterResolvent S t ht f) w.fst =
      ((1 - t : ℝ) : ℂ) * inner ℂ (parameterResolvent S t ht f) w.fst := by
    rw [← algebraMap_smul ℂ (1 - t), inner_smul_left]
    simp
  rw [hsm] at hh
  change inner ℂ (parameterResolvent S t ht f) w.fst +
    inner ℂ (parameterEnergySolution S t ht f).snd w.snd =
      inner ℂ f w.fst + ((1 - t : ℝ) : ℂ) * inner ℂ (parameterResolvent S t ht f) w.fst at hh
  push_cast at hh
  linear_combination hh

end
end krylov.Strings.GeneralSpectral
