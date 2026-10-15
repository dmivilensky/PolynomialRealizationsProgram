import «2610.05164v2».Comparison.ProfileLipschitz
import «2610.05164v2».Calibration.BaseIdentity

/-!
Article: 2610.05164v2, Theorem 3.4.
Lemma 12: signed coefficients and integrability for every comparison profile.
Use: `«2610.05164v2».Comparison.Profile.comparisonA0_integrable` feeds
`«2610.05164v2».Primal.traceDifferenceDensity_integrable` (trace Difference Density integrable).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_trace_comparison` — 2610.05164v2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Comparison
set_option backward.isDefEq.respectTransparency false
section Static
variable {κ : ℝ} (P : «2610.05164v2».Comparison.Profile κ)

/--
Defines `comparisonA` of type `ℝ` by `if q ∈ Ioo (0:ℝ) 2 then determinantCoefficient κ s q
(P.speed q) r (P.rightFilter hκ s q) else 0`.

Use: `«2610.05164v2».Comparison.Profile.comparisonA_bound` rewrites with this definition to
establish the stated quantitative bound `‖P.comparisonA hκ s q r‖ ≤ (s/2*P.C)*P.amplitude q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonA (hκ : 0 < κ) (s q r : ℝ) : ℝ :=
  if q ∈ Ioo (0:ℝ) 2 then
    determinantCoefficient κ s q (P.speed q) r (P.rightFilter hκ s q) else 0
/--
Defines `comparisonA0` of type `ℝ` by `if q ∈ Ioo (0:ℝ) 2 then traceCoefficient κ q (P.speed q)
r (P.rightLinear hκ q) else 0`.

Use: `«2610.05164v2».Comparison.Profile.comparisonA0_bound` rewrites with this definition to
establish the stated quantitative bound `‖P.comparisonA0 hκ q r‖ ≤ (κ*P.C)*P.amplitude q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonA0 (hκ : 0 < κ) (q r : ℝ) : ℝ :=
  if q ∈ Ioo (0:ℝ) 2 then
    traceCoefficient κ q (P.speed q) r (P.rightLinear hκ q) else 0

/--
The stated quantitative bound `‖P.comparisonA hκ s q r‖ ≤ (s/2*P.C)*P.amplitude q`.

Use: `«2610.05164v2».Comparison.Profile.comparisonA_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => P.comparisonA
G.coupling_positive s (G.q x) (nonlinear s m x)* (m x-(P.amplitude (G.q x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem comparisonA_bound {s q r : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hq : q ∈ Icc (0:ℝ) 2) (hr : r ∈ Icc (0:ℝ) (s/κ*q)) :
    ‖P.comparisonA hκ s q r‖ ≤ (s/2*P.C)*P.amplitude q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · rw [comparisonA,ite_eq_left hi]
    have hR := P.rightFilter_bounds hκ hs hq
    have hb := determinantCoefficient_bounds hκ hs hq (P.speed_pos hi) hr.1 hR.1 hr.2 hR.2
    rw [Real.norm_eq_abs,abs_of_nonpos hb.2]
    have hQ := P.Q_div_speed_le_amplitude hi
    have h := mul_le_mul_of_nonneg_left hQ (show 0 ≤ s/2 by positivity)
    calc
      _ ≤ s*«2610.05164v2».Calibration.Q q/(2*P.speed q) := by
        simpa only [neg_mul,neg_div,neg_neg] using neg_le_neg hb.1
      _ ≤ (s/2*P.C)*P.amplitude q := by convert h using 1 <;> ring
  · rw [comparisonA,ite_eq_right hi,norm_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg hs (by norm_num)) P.C_positive.le) (P.nonneg q hq)

/--
The stated quantitative bound `‖P.comparisonA0 hκ q r‖ ≤ (κ*P.C)*P.amplitude q`.

Use: `«2610.05164v2».Comparison.Profile.comparisonA0_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => P.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(P.amplitude (G.q x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem comparisonA0_bound {q r : ℝ} (hκ : 0 < κ)
    (hq : q ∈ Icc (0:ℝ) 2) (hr : r ∈ Icc (0:ℝ) q) :
    ‖P.comparisonA0 hκ q r‖ ≤ (κ*P.C)*P.amplitude q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · rw [comparisonA0,ite_eq_left hi]
    have hR := P.rightLinear_bounds hκ hq
    have hb := traceCoefficient_bounds hκ hq (P.speed_pos hi) hr hR
    rw [Real.norm_eq_abs,abs_of_nonpos hb.2]
    have h := mul_le_mul_of_nonneg_left (P.Q_div_speed_le_amplitude hi) hκ.le
    calc
      _ ≤ κ*«2610.05164v2».Calibration.Q q/P.speed q := by
        simpa only [neg_mul,neg_div,neg_neg] using neg_le_neg hb.1
      _ ≤ (κ*P.C)*P.amplitude q := by convert h using 1 <;> ring
  · rw [comparisonA0,ite_eq_right hi,norm_zero]
    exact mul_nonneg (mul_nonneg hκ.le P.C_positive.le) (P.nonneg q hq)

/--
Membership in the specified domain/enclosure: `P.comparisonA hκ s q r ∈ Icc
(-s*«2610.05164v2».Calibration.Q q/(2*P.speed q)) 0`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.4.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightFilter_bounds`,
`«2610.05164v2».Comparison.determinantCoefficient_bounds`,
`«2610.05164v2».Comparison.Profile.speed_pos` with the arguments shown in the proof.
-/
theorem comparisonA_sharp {s q r : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hq : q ∈ Ioo (0:ℝ) 2) (hr : r ∈ Icc (0:ℝ) (s/κ*q)) :
    P.comparisonA hκ s q r ∈ Icc (-s*«2610.05164v2».Calibration.Q q/(2*P.speed q)) 0 := by
  rw [comparisonA,ite_eq_left hq]
  have hR := P.rightFilter_bounds hκ hs ⟨hq.1.le,hq.2.le⟩
  exact determinantCoefficient_bounds hκ hs ⟨hq.1.le,hq.2.le⟩ (P.speed_pos hq) hr.1 hR.1 hr.2 hR.2

/--
Membership in the specified domain/enclosure: `P.comparisonA0 hκ q r ∈ Icc
(-κ*«2610.05164v2».Calibration.Q q/P.speed q) 0`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.4.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.traceCoefficient_bounds`,
`«2610.05164v2».Comparison.Profile.speed_pos`,
`«2610.05164v2».Comparison.Profile.rightLinear_bounds` with the arguments shown in the proof.
-/
theorem comparisonA0_sharp {q r : ℝ} (hκ : 0 < κ)
    (hq : q ∈ Ioo (0:ℝ) 2) (hr : r ∈ Icc (0:ℝ) q) :
    P.comparisonA0 hκ q r ∈ Icc (-κ*«2610.05164v2».Calibration.Q q/P.speed q) 0 := by
  rw [comparisonA0,ite_eq_left hq]
  exact traceCoefficient_bounds hκ ⟨hq.1.le,hq.2.le⟩ (P.speed_pos hq) hr
    (P.rightLinear_bounds hκ ⟨hq.1.le,hq.2.le⟩)

end Static
section Along
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
  (P : «2610.05164v2».Comparison.Profile (groundParameter hm hn))

/--
Integrability of the displayed function: `Integrable (fun x => (P.amplitude (G.q x))^3)`.

Use: `«2610.05164v2».Comparison.Profile.amplitude_defect_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (fun x => w x*(m
x-(P.amplitude (G.q x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_mem`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_integrability` with the arguments shown in
the proof.
-/
theorem amplitude_cube_integrable : Integrable (fun x => (P.amplitude (G.q x))^3) := by
  have hc := P.continuous.comp_continuous G.R.q_continuous G.coordinate_mem
  apply (G.coordinate_integrability.1.const_mul P.C).mono' (hc.pow 3).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖(P.amplitude (G.q x))^3‖ ≤ P.C*«2610.05164v2».Calibration.Q (G.q x)
    rw [Real.norm_of_nonneg (pow_nonneg (P.nonneg _ (G.coordinate_mem x)) 3)]
    exact P.cube_bound (G.coordinate_mem x))

/--
Integrability of the displayed function: `Integrable (fun x => P.amplitude (G.q x)*m x)`.

Use: `«2610.05164v2».Comparison.Profile.amplitude_defect_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (fun x => w x*(m
x-(P.amplitude (G.q x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_mem`,
`«2610.05164v2».Comparison.Profile.amplitude_le_bound` with the arguments shown in the proof.
-/
theorem amplitude_mul_density_integrable : Integrable (fun x => P.amplitude (G.q x)*m x) := by
  have hc := P.continuous.comp_continuous G.R.q_continuous G.coordinate_mem
  exact hm.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (P.nonneg _ (G.coordinate_mem x))]
    exact P.amplitude_le_bound (G.coordinate_mem x)))

/--
Integrability of the displayed function: `Integrable (fun x => w x*(m x-(P.amplitude (G.q
x))^2))`.

Use: `«2610.05164v2».Comparison.Profile.comparisonA0_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (fun x => P.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(P.amplitude (G.q x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_mem`,
`«2610.05164v2».Comparison.Profile.amplitude_mul_density_integrable` with the arguments shown
in the proof.
-/
theorem amplitude_defect_integrable {w : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hw : AEStronglyMeasurable w) (hb : ∀ x, ‖w x‖ ≤ A*P.amplitude (G.q x)) :
    Integrable (fun x => w x*(m x-(P.amplitude (G.q x))^2)) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
  -- `«2610.05164v2».GroundState.GroundWitness.coordinate_mem`,
  -- `«2610.05164v2».Comparison.Profile.amplitude_mul_density_integrable` with the arguments
  -- shown in the proof.
  have hν := (P.continuous).comp_continuous
    G.R.q_continuous G.coordinate_mem
  apply (((amplitude_mul_density_integrable G P).add (amplitude_cube_integrable G P)).const_mul A).mono'
  · exact hw.mul (hm.aestronglyMeasurable.sub (hν.pow 2).aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => by
      have hv := P.nonneg _ (G.coordinate_mem x)
      rw [norm_mul]
      calc
        _ ≤ (A*P.amplitude (G.q x))*(m x+
            (P.amplitude (G.q x))^2) :=
          mul_le_mul (hb x) ((norm_sub_le _ _).trans (by
            rw [Real.norm_of_nonneg (hn x),Real.norm_of_nonneg (sq_nonneg _)]))
            (norm_nonneg _) (mul_nonneg hA hv)
        _ = A*(P.amplitude (G.q x)*m x+
            (P.amplitude (G.q x))^3) := by ring)

/--
Integrability of the displayed function: `Integrable (fun x => P.comparisonA
G.coupling_positive s (G.q x) (nonlinear s m x)* (m x-(P.amplitude (G.q x))^2))`.

Use: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` uses this integrability
result to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».GroundState.RiccatiData.q_continuous`,
`«2610.05164v2».Filters.nonlinear_continuous` with the arguments shown in the proof.
-/
theorem comparisonA_integrable {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x => P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
      (m x-(P.amplitude (G.q x))^2)) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
  -- `«2610.05164v2».Filters.nonlinear_continuous` with the arguments shown in the proof.
  have hq := G.R.q_continuous.measurable
  have hD : Measurable (fun x => P.speed (G.q x)) :=
    (P.speedData G.coupling_positive).measurable.comp hq
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR : Continuous (fun x => P.rightFilter G.coupling_positive s (G.q x)) :=
    ((nonlinear_continuous
      (reflected_integrable ((P.speedData G.coupling_positive).density_integrable G.coupling_positive))
      (reflected_nonneg ((P.speedData G.coupling_positive).density_nonneg G.coupling_positive)) hs).comp
      (P.speedData G.coupling_positive).X_continuous.neg).comp G.R.q_continuous
  have hr := (nonlinear_continuous hm hn hs).measurable
  have hw : Measurable (fun x => P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)) := by
    unfold comparisonA determinantCoefficient
    apply Measurable.ite (measurableSet_Ioo.preimage hq)
    · unfold «2610.05164v2».Calibration.Q
      exact ((measurable_const.mul (hq.mul (measurable_const.sub hq))).add
        ((measurable_const.mul hr).mul hR.measurable)).neg.div
          (hD.mul ((measurable_const.add hr).add hR.measurable))
    · fun_prop
  apply amplitude_defect_integrable G P (A := (s/2*P.C))
    (mul_nonneg (div_nonneg hs (by norm_num)) P.C_positive.le) hw.aestronglyMeasurable
  intro x
  exact P.comparisonA_bound G.coupling_positive hs (G.coordinate_mem x)
    ⟨(nonlinear_bounds hm hn hs x).1,nonlinear_le_coordinate G hs x⟩

/--
Integrability of the displayed function: `Integrable (fun x => P.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(P.amplitude (G.q x))^2))`.

Use: `«2610.05164v2».Comparison.Profile.signed_trace_comparison` uses this integrability result
to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».GroundState.RiccatiData.q_continuous`,
`«2610.05164v2».Filters.causal_continuous` with the arguments shown in the proof.
-/
theorem comparisonA0_integrable :
    Integrable (fun x => P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
      (m x-(P.amplitude (G.q x))^2)) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
  -- `«2610.05164v2».Filters.causal_continuous` with the arguments shown in the proof.
  have hq := G.R.q_continuous.measurable
  have hD : Measurable (fun x => P.speed (G.q x)) :=
    (P.speedData G.coupling_positive).measurable.comp hq
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR : Continuous (fun x => P.rightLinear G.coupling_positive (G.q x)) :=
    (((causal_continuous (by norm_num : (0:ℝ) ≤ 2)
      (reflected_integrable ((P.speedData G.coupling_positive).density_integrable G.coupling_positive))).comp
      (P.speedData G.coupling_positive).X_continuous.neg).const_mul _).comp G.R.q_continuous
  -- Establish continuity hr before using the function at limits or in calculus arguments.
  have hr : Continuous (linear hm hn) :=
    (causal_continuous (by norm_num : (0:ℝ) ≤ 2) hm).const_mul _
  have hw : Measurable (fun x => P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)) := by
    unfold comparisonA0 traceCoefficient
    apply Measurable.ite (measurableSet_Ioo.preimage hq)
    · unfold «2610.05164v2».Calibration.Q
      exact (measurable_const.mul (((measurable_const.mul hr.measurable).mul hR.measurable).sub
        ((hq.mul (measurable_const.sub hq)).mul (hr.measurable.add hR.measurable)))).div
          (measurable_const.mul hD)
    · fun_prop
  apply amplitude_defect_integrable G P (A := (groundParameter hm hn*P.C))
    (mul_nonneg G.coupling_positive.le P.C_positive.le) hw.aestronglyMeasurable
  intro x
  exact P.comparisonA0_bound G.coupling_positive (G.coordinate_mem x)
    ⟨linear_nonneg G x,linear_le_coordinate G x⟩

end Along
end
end «2610.05164v2».Comparison.Profile
