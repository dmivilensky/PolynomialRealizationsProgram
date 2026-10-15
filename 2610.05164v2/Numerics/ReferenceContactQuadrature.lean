import «2610.05164v2».Numerics.ReferenceCoreSource
import «2610.05164v2».Numerics.ActualJetQuadrature
import «2610.05164v2».Numerics.RationalExpr

/-!
Article: 2610.05164v2, Section 4.1.
Finite reference-core quadrature plus the checked logarithmic exterior term bounds the actual
calibration J(2).
Use: `«2610.05164v2».Numerics.ReferenceCoreSource.vacuumExpression_enclose` feeds
`«2610.05164v2».Certificates.Compact.ReferenceConstant.tail_mem` (tail mem).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.ReferenceCoreSource
open Set MeasureTheory LeanCert.Core «2610.05164v2».Calibration «2610.05164v2».Certificates
open scoped IntervalExpr
set_option autoImplicit false
set_option maxHeartbeats 2000000

/--
Defines `vacuumExpression` of type `IntervalExpr 1` by `((.literal sigma)*(.variable
0)-2*(.logarithm (1+(.literal (sigma/2))*(.variable 0)) terms))/(.literal (sigma^2))`.

Use: `«2610.05164v2».Numerics.ReferenceCoreSource.vacuumExpression_value` rewrites with this
definition to establish the identity `(vacuumExpression sigma terms).value (fun _ =>
w)=ReferenceData.vacuumSquare (sigma:ℝ) w`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def vacuumExpression (sigma : ℚ) (terms : ℕ) : IntervalExpr 1 :=
  ((.literal sigma)*(.variable 0)-2*(.logarithm
    (1+(.literal (sigma/2))*(.variable 0)) terms))/(.literal (sigma^2))

/--
Exact identity `(vacuumExpression sigma terms).value (fun _ => w)=ReferenceData.vacuumSquare
(sigma:ℝ) w`.

Use: `«2610.05164v2».Numerics.ReferenceCoreSource.vacuumExpression_enclose` rewrites with this
identity to establish membership in the specified domain/enclosure: `ReferenceData.vacuumSquare
(sigma:ℝ) w∈T`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem vacuumExpression_value (sigma : ℚ) (terms : ℕ) (w : ℝ) :
    (vacuumExpression sigma terms).value (fun _ => w)=ReferenceData.vacuumSquare (sigma:ℝ) w := by
  simp only [vacuumExpression,IntervalExpr.value_div,IntervalExpr.value_sub,
    IntervalExpr.value,ReferenceData.vacuumSquare,
    Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow]
  rw [show (sigma:ℝ)/2*w=(sigma:ℝ)*w/2 by ring]
  norm_num

/--
Membership in the specified domain/enclosure: `ReferenceData.vacuumSquare (sigma:ℝ) w∈T`.

Use: `«2610.05164v2».Numerics.ReferenceCoreSource.calibration_constant_enclosed` uses this
assertion to establish membership in the specified domain/enclosure: `(R.calibration (σ :=
(sigma:ℝ)) (by exact_mod_cast hsigma) hb ho).J 2∈IntervalRat.sub H T`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceCoreSource.vacuumExpression_value`,
`«2610.05164v2».Numerics.IntervalExpr.enclose_sound` with the arguments shown in the proof.
-/
theorem vacuumExpression_enclose {sigma : ℚ} {terms : ℕ} {W T : IntervalRat}
    (hc : (vacuumExpression sigma terms).enclose (fun _ => W)=some T)
    {w : ℝ} (hw : w∈W) : ReferenceData.vacuumSquare (sigma:ℝ) w∈T := by
  rw [←vacuumExpression_value sigma terms w]
  exact IntervalExpr.enclose_sound _ _ hc (fun _ => hw)

/--
Membership in the specified domain/enclosure: `(R.calibration (σ := (sigma:ℝ)) (by
exact_mod_cast hsigma) hb ho).J 2∈IntervalRat.sub H T`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized`,
`«2610.05164v2».Numerics.actualJetIntegralBox_sound_on`,
`«2610.05164v2».Calibration.ReferenceData.contactCoreIntegrand_smooth` with the arguments shown
in the proof.
-/
theorem calibration_constant_enclosed (R : ReferenceData) {sigma : ℚ}
    (hsigma : 0<sigma) {b omega : ℝ} (hb : 0<b) (ho : 0≤omega) {n : ℕ}
    (cells : List (ActualJetCell (R.contactCoreIntegrand (σ := (sigma:ℝ))
      (by exact_mod_cast hsigma)) (n+1)))
    (hp : PartitionFrom 0 1 (cells.map ActualJetCell.domain))
    {H W T : IntervalRat}
    (hH : intervalSubsetCheck (actualJetIntegralBox cells) H=true)
    (hW : R.normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) 0∈W)
    {terms : ℕ} (hT : (vacuumExpression sigma terms).enclose (fun _ => W)=some T) :
    (R.calibration (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) hb ho).J 2∈IntervalRat.sub H T := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized`,
  -- `«2610.05164v2».Numerics.actualJetIntegralBox_sound_on`,
  -- `«2610.05164v2».Calibration.ReferenceData.contactCoreIntegrand_smooth` with the arguments
  -- shown in the proof.
  rw [R.calibration_constant_normalized (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) hb ho]
  apply IntervalRat.mem_sub _ (vacuumExpression_enclose hT hW)
  have hi := actualJetIntegralBox_sound_on cells hp (by
    simpa only [Rat.cast_zero,Rat.cast_one] using
      (R.contactCoreIntegrand_smooth (σ := (sigma:ℝ))
        (by exact_mod_cast hsigma)).of_le (by simp))
  apply intervalSubsetCheck_sound hH
  simpa only [Rat.cast_zero,Rat.cast_one,intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using hi

end «2610.05164v2».Numerics.ReferenceCoreSource
