import «2610.05164v2».StateRegion.SharpBounds

/-!
Article: 2610.05164v2, Proposition 7.
Mixtures.
Use: `«2610.05164v2».StateRegion.twoPoint_integral` feeds
`«2610.05164v2».StateRegion.Scales.attain_thetaPlus` (attain theta Plus).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».StateRegion
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
Defines `mixture` of type `Measure ℝ` by `ENNReal.ofReal (1-p) • μ + ENNReal.ofReal p • ν`.

Use: `«2610.05164v2».StateRegion.mixture_integral` rewrites with this definition to establish
exact identity `(∫ w, F w ∂mixture p μ ν)=(1-p)*(∫ w, F w ∂μ)+p*(∫ w, F w ∂ν)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def mixture (p : ℝ) (μ ν : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1-p) • μ + ENNReal.ofReal p • ν

/--
The precise assertion is `IsProbabilityMeasure (mixture p μ ν)`.

Use: `«2610.05164v2».StateRegion.twoPoint_probability` uses this assertion to establish the
precise assertion is `IsProbabilityMeasure (twoPoint p lo hi)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mixture_probability {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (mixture p μ ν) := by
  constructor
  simp only [mixture,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
  simp

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂mixture p μ ν, w ∈ Icc
(0:ℝ) 1`.

Use: `«2610.05164v2».StateRegion.twoPoint_supported` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂twoPoint p lo hi, w ∈ Icc
(0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem mixture_supported {p : ℝ} {μ ν : Measure ℝ}
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) (hν : ∀ᵐ w ∂ν, w ∈ Icc (0:ℝ) 1) :
    ∀ᵐ w ∂mixture p μ ν, w ∈ Icc (0:ℝ) 1 :=
  ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hμ _,Measure.ae_smul_measure hν _⟩
/--
Exact identity `(∫ w, F w ∂mixture p μ ν)=(1-p)*(∫ w, F w ∂μ)+p*(∫ w, F w ∂ν)`.

Use: `«2610.05164v2».StateRegion.twoPoint_integral` rewrites with this identity to establish
exact identity `(∫ w, F w ∂twoPoint p lo hi)=(1-p)*F lo+p*F hi`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mixture_integral {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) {μ ν : Measure ℝ}
    {F : ℝ → ℝ} (hμ : Integrable F μ) (hν : Integrable F ν) :
    (∫ w, F w ∂mixture p μ ν)=(1-p)*(∫ w, F w ∂μ)+p*(∫ w, F w ∂ν) := by
  rw [mixture,integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
    (hν.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure,ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2),
    ENNReal.toReal_ofReal hp.1,smul_eq_mul]

/--
Defines `twoPoint` of type `Measure ℝ` by `mixture p (Measure.dirac lo) (Measure.dirac hi)`.

Use: `«2610.05164v2».StateRegion.twoPoint_integral` rewrites with this definition to establish
exact identity `(∫ w, F w ∂twoPoint p lo hi)=(1-p)*F lo+p*F hi`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def twoPoint (p lo hi : ℝ) : Measure ℝ := mixture p (Measure.dirac lo) (Measure.dirac hi)

/--
The precise assertion is `IsProbabilityMeasure (twoPoint p lo hi)`.

Use: `«2610.05164v2».StateRegion.Scales.attain_thetaMinus` uses this assertion to establish the
precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaMinus u t))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.mixture_probability` with the
arguments shown in the proof.
-/
theorem twoPoint_probability {p lo hi : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    IsProbabilityMeasure (twoPoint p lo hi) := mixture_probability hp _ _

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂twoPoint p lo hi, w ∈ Icc
(0:ℝ) 1`.

Use: `«2610.05164v2».StateRegion.Scales.attain_thetaMinus` uses this assertion to establish the
precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaMinus u t))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.mixture_supported` with the
arguments shown in the proof.
-/
theorem twoPoint_supported {p lo hi : ℝ} (hlo : lo ∈ Icc (0:ℝ) 1) (hhi : hi ∈ Icc (0:ℝ) 1) :
    ∀ᵐ w ∂twoPoint p lo hi, w ∈ Icc (0:ℝ) 1 :=
  mixture_supported ((ae_dirac_iff measurableSet_Icc).mpr hlo)
    ((ae_dirac_iff measurableSet_Icc).mpr hhi)

/--
Exact identity `(∫ w, F w ∂twoPoint p lo hi)=(1-p)*F lo+p*F hi`.

Use: `«2610.05164v2».StateRegion.Scales.attain_thetaMinus` rewrites with this identity to
establish the precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaMinus u t))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.mixture_integral` with the
arguments shown in the proof.
-/
theorem twoPoint_integral {p lo hi : ℝ} (hp : p ∈ Icc (0:ℝ) 1) (F : ℝ → ℝ) :
    (∫ w, F w ∂twoPoint p lo hi)=(1-p)*F lo+p*F hi := by
  rw [twoPoint,mixture_integral hp (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness)),
    integral_dirac,integral_dirac]

end
end «2610.05164v2».StateRegion
