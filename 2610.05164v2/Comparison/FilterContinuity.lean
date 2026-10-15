import «2610.05164v2».Comparison.FilterStability

/-!
Article: 2610.05164v2, Lemma 11.
Lemma 13: joint continuity of the actual nonlinear comparison filter, including both ends of the
closed ground-coordinate interval.
Use: `«2610.05164v2».Calibration.Data.leftFilter_joint_continuous` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.farFilter_joint_continuous` (far Filter joint
continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data) {s : ℝ} (hs : 0 ≤ s)
include hs

/--
Continuity of the displayed function: `Continuous (fun p : Ioi (0:ℝ) × Icc (0:ℝ) 2 =>
C.leftFilter p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_joint_continuous` uses this
continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.defect p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem leftFilter_joint_continuous :
    Continuous (fun p : Ioi (0:ℝ) × Icc (0:ℝ) 2 => C.leftFilter p.1.property s p.2) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  -- Record the convergence hκ with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hκ : Tendsto (fun z : Ioi (0:ℝ) × Icc (0:ℝ) 2 => (z.1:ℝ)) (𝓝 p) (𝓝 (p.1:ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.tendsto
  -- Record the convergence hq with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hq : Tendsto (fun z : Ioi (0:ℝ) × Icc (0:ℝ) 2 => (z.2:ℝ)) (𝓝 p) (𝓝 (p.2:ℝ)) :=
    (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto
  have hE := (C.filterError_tendsto (s := s) p.1.property).comp hκ
  -- Record the convergence hF with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hF : Tendsto (fun z : Ioi (0:ℝ) × Icc (0:ℝ) 2 =>
      |C.leftFilter p.1.property s z.2-C.leftFilter p.1.property s p.2|) (𝓝 p) (𝓝 0) := by
    simpa only [Function.comp_apply,sub_self,abs_zero] using
      (((C.leftFilter_continuous p.1.property hs).continuousAt.tendsto.comp hq).sub_const
        (C.leftFilter p.1.property s p.2)).abs
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa only [add_zero] using hE.add hF)
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |C.leftFilter z.1.property s z.2-C.leftFilter p.1.property s z.2|+
      |C.leftFilter p.1.property s z.2-C.leftFilter p.1.property s p.2| :=
      abs_sub_le _ _ _
    _ ≤ C.filterError z.1 p.1 s+|C.leftFilter p.1.property s z.2-C.leftFilter p.1.property s p.2| :=
      add_le_add (C.leftFilter_parameter_bound z.1.property p.1.property hs z.2.property) le_rfl

end
end «2610.05164v2».Calibration.Data
