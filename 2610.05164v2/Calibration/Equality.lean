import «2610.05164v2».Calibration.BaseIdentity

/-!
Article: 2610.05164v2, Proposition 5.
The exact equality conditions in the base identity.
Use: `«2610.05164v2».Calibration.Data.energy_eq_base_iff` feeds
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` (self Consistent attainment).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` — 2610.05164v2,
Proposition 5; Self-consistent reference and all equality cases.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data)
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)

/--
The base bound is attained precisely when the amplitude defect and the weighted contact defect
vanish almost everywhere. No reference profile is postulated in this characterization.

Use: `«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment` uses this identity to
establish the precise assertion is `(∫ x, (sqrt (R.density x))^3)= (R.calibration hσ hb
hω).base R.k (logDeterminant (kernelEigenvalue R.density_properties.1 R.density_properties.2.1)
(σ*R.k))`.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.rho_integrable`,
`«2610.05164v2».Calibration.Data.T_integrable`, `«2610.05164v2».Calibration.rho_nonneg` with
the arguments shown in the proof.
-/
theorem energy_eq_base_iff (hM : (∫ x, m x)=1)
    (hE : Integrable (fun x => (sqrt (m x))^3)) :
    (∫ x, (sqrt (m x))^3)=C.base (groundParameter hm hn)
      («2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue hm hn)
        (C.sigma*groundParameter hm hn)) ↔
      ∀ᵐ x, sqrt (m x)=C.amplitude (groundParameter hm hn) (G.q x) ∧
        C.omega*C.T (G.q x) (C.calibrationState G x)=0 := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.rho_integrable`,
  -- `«2610.05164v2».Calibration.Data.T_integrable`, `«2610.05164v2».Calibration.rho_nonneg`
  -- with the arguments shown in the proof.
  let D : ℝ → ℝ := fun x => rho (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x))+
    C.omega*C.T (G.q x) (C.calibrationState G x)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable D := (C.rho_integrable G hE).add ((C.T_integrable G).const_mul C.omega)
  have hp (x : ℝ) : 0 ≤ D x := add_nonneg
    (rho_nonneg (sqrt_nonneg _) (C.amplitude_nonneg G.coupling_positive _))
    (mul_nonneg C.omega_nonneg (C.T_nonneg G x))
  have hz : (∀ᵐ x, D x=0) ↔ ∀ᵐ x, sqrt (m x)=C.amplitude (groundParameter hm hn) (G.q x) ∧
      C.omega*C.T (G.q x) (C.calibrationState G x)=0 := by
    apply eventually_congr
    apply Eventually.of_forall
    intro x
    have hnρ := rho_nonneg (sqrt_nonneg (m x)) (C.amplitude_nonneg G.coupling_positive (G.q x))
    have hnT := mul_nonneg C.omega_nonneg (C.T_nonneg G x)
    have hρ := rho_eq_zero_iff (sqrt_nonneg (m x)) (C.amplitude_nonneg G.coupling_positive (G.q x))
    change (rho (sqrt (m x)) (C.amplitude (groundParameter hm hn) (G.q x))+
      C.omega*C.T (G.q x) (C.calibrationState G x)=0) ↔ _
    rw [add_eq_zero_iff_of_nonneg hnρ hnT,hρ]
  have hi0 : ((∫ x, D x)=0) ↔ ∀ᵐ x, D x=0 := by
    simpa only [Filter.EventuallyEq,Pi.zero_apply] using integral_eq_zero_iff_of_nonneg hp hi
  rw [← hz,← hi0,C.base_identity G hM hE]
  change (_+∫ x, D x=_ ) ↔ (∫ x, D x)=0
  constructor <;> intro h <;> linarith

end
end «2610.05164v2».Calibration.Data
