import «2610.05164v2».Comparison.Coefficients
import «2610.05164v2».Comparison.RightFilters
import «2610.05164v2».Calibration.BaseIdentity

/-!
Article: 2610.05164v2, Proposition 8.
Theorem 3.4's actual coefficients, including the endpoint convention, sharp signs, and integrability
along the full L1 ground-state class.
Use: `«2610.05164v2».Calibration.Data.comparisonA0_integrable` feeds
`«2610.05164v2».Calibration.Data.comparisonDefect_integral` (comparison Defect integral).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Comparison
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data)

/--
Defines `comparisonA` of type `ℝ` by `if q ∈ Ioo (0:ℝ) 2 then determinantCoefficient κ s q
(C.speed κ q) r (C.rightFilter hκ s q) else 0`.

Use: `«2610.05164v2».Calibration.Data.comparisonA_bound` rewrites with this definition to
establish the stated quantitative bound `‖C.comparisonA hκ s q r‖ ≤ s/(4*C.b)*C.amplitude κ q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonA {κ : ℝ} (hκ : 0 < κ) (s q r : ℝ) : ℝ :=
  if q ∈ Ioo (0:ℝ) 2 then
    determinantCoefficient κ s q (C.speed κ q) r (C.rightFilter hκ s q) else 0
/--
Defines `comparisonA0` of type `ℝ` by `if q ∈ Ioo (0:ℝ) 2 then traceCoefficient κ q (C.speed κ
q) r (C.rightLinear hκ q) else 0`.

Use: `«2610.05164v2».Calibration.Data.comparisonA0_bound` rewrites with this definition to
establish the stated quantitative bound `‖C.comparisonA0 hκ q r‖ ≤ κ/(2*C.b)*C.amplitude κ q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonA0 {κ : ℝ} (hκ : 0 < κ) (q r : ℝ) : ℝ :=
  if q ∈ Ioo (0:ℝ) 2 then
    traceCoefficient κ q (C.speed κ q) r (C.rightLinear hκ q) else 0

/--
The stated quantitative bound `«2610.05164v2».Calibration.Q q/C.speed κ q ≤ C.amplitude κ
q/(2*C.b)`.

Use: `«2610.05164v2».Calibration.Data.comparisonA0_bound` uses this bound to establish the
stated quantitative bound `‖C.comparisonA0 hκ q r‖ ≤ κ/(2*C.b)*C.amplitude κ q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_spec`,
`«2610.05164v2».Calibration.Data.speed_positive`,
`«2610.05164v2».Calibration.Data.Q_div_speed_amplitude` with the arguments shown in the proof.
-/
theorem Q_div_speed_le_amplitude {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    «2610.05164v2».Calibration.Q q/C.speed κ q ≤ C.amplitude κ q/(2*C.b) := by
  have hv := (C.amplitude_spec hκ hq).1
  have hd := C.speed_positive hκ hq
  have hb : 0 < 2*C.b := by linarith [C.b_positive]
  have h := (div_le_div_iff₀ (mul_pos hd hv) hb).mp (C.Q_div_speed_amplitude hκ hq)
  exact (div_le_div_iff₀ hd hb).mpr (by simpa only [one_mul,mul_comm] using h)

/--
The stated quantitative bound `‖C.comparisonA hκ s q r‖ ≤ s/(4*C.b)*C.amplitude κ q`.

Use: `«2610.05164v2».Calibration.Data.comparisonA_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => C.comparisonA
G.coupling_positive s (G.q x) (nonlinear s m x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem comparisonA_bound {κ s q r : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hq : q ∈ Icc (0:ℝ) 2) (hr : r ∈ Icc (0:ℝ) (s/κ*q)) :
    ‖C.comparisonA hκ s q r‖ ≤ s/(4*C.b)*C.amplitude κ q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · rw [comparisonA,ite_eq_left hi]
    have hR := C.rightFilter_bounds hκ hs hq
    have hb := determinantCoefficient_bounds hκ hs hq (C.speed_positive hκ hi) hr.1 hR.1 hr.2 hR.2
    rw [Real.norm_eq_abs,abs_of_nonpos hb.2]
    have hQ := C.Q_div_speed_le_amplitude hκ hi
    have h := mul_le_mul_of_nonneg_left hQ (show 0 ≤ s/2 by positivity)
    calc
      _ ≤ s*«2610.05164v2».Calibration.Q q/(2*C.speed κ q) := by
        simpa only [neg_mul,neg_div,neg_neg] using neg_le_neg hb.1
      _ ≤ s/(4*C.b)*C.amplitude κ q := by convert h using 1 <;> ring
  · rw [comparisonA,ite_eq_right hi,norm_zero]
    exact mul_nonneg (div_nonneg hs (by linarith [C.b_positive])) (C.amplitude_nonneg hκ q)

/--
The stated quantitative bound `‖C.comparisonA0 hκ q r‖ ≤ κ/(2*C.b)*C.amplitude κ q`.

Use: `«2610.05164v2».Calibration.Data.comparisonA0_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem comparisonA0_bound {κ q r : ℝ} (hκ : 0 < κ)
    (hq : q ∈ Icc (0:ℝ) 2) (hr : r ∈ Icc (0:ℝ) q) :
    ‖C.comparisonA0 hκ q r‖ ≤ κ/(2*C.b)*C.amplitude κ q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · rw [comparisonA0,ite_eq_left hi]
    have hR := C.rightLinear_bounds hκ hq
    have hb := traceCoefficient_bounds hκ hq (C.speed_positive hκ hi) hr hR
    rw [Real.norm_eq_abs,abs_of_nonpos hb.2]
    have h := mul_le_mul_of_nonneg_left (C.Q_div_speed_le_amplitude hκ hi) hκ.le
    calc
      _ ≤ κ*«2610.05164v2».Calibration.Q q/C.speed κ q := by
        simpa only [neg_mul,neg_div,neg_neg] using neg_le_neg hb.1
      _ ≤ κ/(2*C.b)*C.amplitude κ q := by convert h using 1 <;> ring
  · rw [comparisonA0,ite_eq_right hi,norm_zero]
    exact mul_nonneg (div_nonneg hκ.le (by linarith [C.b_positive])) (C.amplitude_nonneg hκ q)

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)

/--
Integrability of the displayed function: `Integrable (fun x => w x*(m x-(C.amplitude
(groundParameter hm hn) (G.q x))^2))`.

Use: `«2610.05164v2».Calibration.Data.comparisonA0_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (fun x => C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.amplitude_continuousOn_fixed`,
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».GroundState.RiccatiData.q_continuous` with the arguments shown in the proof.
-/
theorem amplitude_defect_integrable {w : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hw : AEStronglyMeasurable w) (hb : ∀ x, ‖w x‖ ≤ A*C.amplitude (groundParameter hm hn) (G.q x)) :
    Integrable (fun x => w x*(m x-(C.amplitude (groundParameter hm hn) (G.q x))^2)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.Data.amplitude_continuousOn_fixed`,
  -- `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».GroundState.RiccatiData.q_continuous` with the arguments shown in the
  -- proof.
  have hν := (C.amplitude_continuousOn_fixed G.coupling_positive).comp_continuous
    G.R.q_continuous G.coordinate_mem
  apply (((C.amplitude_mul_density_integrable G).add (C.amplitude_cube_integrable G)).const_mul A).mono'
  · exact hw.mul (hm.aestronglyMeasurable.sub (hν.pow 2).aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => by
      have hv := C.amplitude_nonneg G.coupling_positive (G.q x)
      rw [norm_mul]
      calc
        _ ≤ (A*C.amplitude (groundParameter hm hn) (G.q x))*(m x+
            (C.amplitude (groundParameter hm hn) (G.q x))^2) :=
          mul_le_mul (hb x) ((norm_sub_le _ _).trans (by
            rw [Real.norm_of_nonneg (hn x),Real.norm_of_nonneg (sq_nonneg _)]))
            (norm_nonneg _) (mul_nonneg hA hv)
        _ = A*(C.amplitude (groundParameter hm hn) (G.q x)*m x+
            (C.amplitude (groundParameter hm hn) (G.q x))^3) := by ring)

/--
Integrability of the displayed function: `Integrable (fun x => C.comparisonA
G.coupling_positive s (G.q x) (nonlinear s m x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Use: `«2610.05164v2».Calibration.Data.comparisonDefect_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (C.comparisonDefect G
ξ₀ ξ₁ χ)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».GroundState.RiccatiData.q_continuous`,
`«2610.05164v2».Filters.nonlinear_continuous` with the arguments shown in the proof.
-/
theorem comparisonA_integrable {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x => C.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
      (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2)) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
  -- `«2610.05164v2».Filters.nonlinear_continuous` with the arguments shown in the proof.
  have hq := G.R.q_continuous.measurable
  have hD : Measurable (fun x => C.speed (groundParameter hm hn) (G.q x)) :=
    (C.comparisonSpeed G.coupling_positive).measurable.comp hq
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR : Continuous (fun x => C.rightFilter G.coupling_positive s (G.q x)) :=
    ((nonlinear_continuous
      (reflected_integrable ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive))
      (reflected_nonneg ((C.comparisonSpeed G.coupling_positive).density_nonneg G.coupling_positive)) hs).comp
      (C.comparisonSpeed G.coupling_positive).X_continuous.neg).comp G.R.q_continuous
  have hr := (nonlinear_continuous hm hn hs).measurable
  have hw : Measurable (fun x => C.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)) := by
    unfold comparisonA determinantCoefficient
    apply Measurable.ite (measurableSet_Ioo.preimage hq)
    · unfold «2610.05164v2».Calibration.Q
      exact ((measurable_const.mul (hq.mul (measurable_const.sub hq))).add
        ((measurable_const.mul hr).mul hR.measurable)).neg.div
          (hD.mul ((measurable_const.add hr).add hR.measurable))
    · fun_prop
  apply C.amplitude_defect_integrable G (A := s/(4*C.b))
    (div_nonneg hs (by linarith [C.b_positive])) hw.aestronglyMeasurable
  intro x
  exact C.comparisonA_bound G.coupling_positive hs (G.coordinate_mem x)
    ⟨(nonlinear_bounds hm hn hs x).1,nonlinear_le_coordinate G hs x⟩

/--
Integrability of the displayed function: `Integrable (fun x => C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Use: `«2610.05164v2».Calibration.Data.comparisonDefect_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (C.comparisonDefect G
ξ₀ ξ₁ χ)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».GroundState.RiccatiData.q_continuous`,
`«2610.05164v2».Filters.causal_continuous` with the arguments shown in the proof.
-/
theorem comparisonA0_integrable :
    Integrable (fun x => C.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)*
      (m x-(C.amplitude (groundParameter hm hn) (G.q x))^2)) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».GroundState.RiccatiData.q_continuous`,
  -- `«2610.05164v2».Filters.causal_continuous` with the arguments shown in the proof.
  have hq := G.R.q_continuous.measurable
  have hD : Measurable (fun x => C.speed (groundParameter hm hn) (G.q x)) :=
    (C.comparisonSpeed G.coupling_positive).measurable.comp hq
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR : Continuous (fun x => C.rightLinear G.coupling_positive (G.q x)) :=
    (((causal_continuous (by norm_num : (0:ℝ) ≤ 2)
      (reflected_integrable ((C.comparisonSpeed G.coupling_positive).density_integrable G.coupling_positive))).comp
      (C.comparisonSpeed G.coupling_positive).X_continuous.neg).const_mul _).comp G.R.q_continuous
  -- Establish continuity hr before using the function at limits or in calculus arguments.
  have hr : Continuous (linear hm hn) :=
    (causal_continuous (by norm_num : (0:ℝ) ≤ 2) hm).const_mul _
  have hw : Measurable (fun x => C.comparisonA0 G.coupling_positive (G.q x) (linear hm hn x)) := by
    unfold comparisonA0 traceCoefficient
    apply Measurable.ite (measurableSet_Ioo.preimage hq)
    · unfold «2610.05164v2».Calibration.Q
      exact (measurable_const.mul (((measurable_const.mul hr.measurable).mul hR.measurable).sub
        ((hq.mul (measurable_const.sub hq)).mul (hr.measurable.add hR.measurable)))).div
          (measurable_const.mul hD)
    · fun_prop
  apply C.amplitude_defect_integrable G (A := groundParameter hm hn/(2*C.b))
    (div_nonneg G.coupling_positive.le (by linarith [C.b_positive])) hw.aestronglyMeasurable
  intro x
  exact C.comparisonA0_bound G.coupling_positive (G.coordinate_mem x)
    ⟨linear_nonneg G x,linear_le_coordinate G x⟩

end
end «2610.05164v2».Calibration.Data
