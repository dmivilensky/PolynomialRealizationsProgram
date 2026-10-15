import «2610.05164v2».DualCertificate.ReferenceFilters
import «2610.05164v2».Calculus.CubicRemoval
import «2610.05164v2».Calculus.DefectOrder

/-!
Article: 2610.05164v2, Theorem 3.6.
F.1(R): the actual reference defect satisfies the regular normalized Riccati equation, with
vanishing initial Taylor data and a smooth cubic quotient.
Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_order_seven` feeds
`«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_zero` (normalized Defect Quotient
zero).
Proof chain: `«2610.05164v2».DualCertificate.Data.Admissible` — 2610.05164v2, Theorem E.1; Stability
of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set Real «2610.05164v2».DualCertificate «2610.05164v2».Calculus
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (R : «2610.05164v2».Calibration.ReferenceData) {σ : ℝ} (hσ : 0<σ)

/--
Exact identity `R.k*(R.normalizedRoot t)^2=R.normalizedSpeed t+t*(2-t^3)`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_derivative` uses this identity
to establish the derivative within the stated domain: `HasDerivWithinAt (R.normalizedDefect hσ)
(R.normalizedDefectRHS hσ t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedSpeed_root {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    R.k*(R.normalizedRoot t)^2=R.normalizedSpeed t+t*(2-t^3) := by
  have he := (R.normalizedRoot_spec ht).2
  unfold cubic at he
  unfold normalizedSpeed
  field_simp [(R.normalizedRoot_spec ht).1.ne']
  linear_combination he

/--
Defines `normalizedDefectRHS` of type `ℝ` by `R.normalizedVelocity t*
((1+σ)*t^6-2*(1+σ*t^3)*R.normalizedDefect hσ t+σ*(R.normalizedDefect hσ t)^2)`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefectRHS_zero` rewrites with this
definition to establish the identity `R.normalizedDefectRHS hσ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def normalizedDefectRHS (t : ℝ) : ℝ := R.normalizedVelocity t*
  ((1+σ)*t^6-2*(1+σ*t^3)*R.normalizedDefect hσ t+σ*(R.normalizedDefect hσ t)^2)

/--
The derivative within the stated domain: `HasDerivWithinAt (R.normalizedDefect hσ)
(R.normalizedDefectRHS hσ t) (Icc (0:ℝ) 1) t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_first_zero` uses this
derivative formula to establish the identity `derivWithin (R.normalizedDefect hσ) (Icc (0:ℝ)
1) 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedDefect_derivative {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (R.normalizedDefect hσ) (R.normalizedDefectRHS hσ t) (Icc (0:ℝ) 1) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd := ((hasDerivWithinAt_id t (Icc (0:ℝ) 1)).pow 3).sub
    (R.normalizedFilter_derivative hσ ht)
  convert! hd using 1
  simp only [id_eq] 
  unfold normalizedDefectRHS normalizedVelocity normalizedDefect
  have he := R.normalizedSpeed_root ht
  field_simp [(R.normalizedSpeed_positive ht).ne']
  linear_combination 3*t^2*he

/--
Exact identity `R.normalizedDefectRHS hσ 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_first_zero` uses this identity
to establish the identity `derivWithin (R.normalizedDefect hσ) (Icc (0:ℝ) 1) 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_zero` with the arguments shown in
the proof.
-/
theorem normalizedDefectRHS_zero : R.normalizedDefectRHS hσ 0=0 := by simp [normalizedDefectRHS,R.normalizedDefect_zero hσ]

/--
Exact identity `derivWithin (R.normalizedDefect hσ) (Icc (0:ℝ) 1) 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_cubic_quotient` uses this
identity to construct witnesses satisfying `∃ g : ℝ → ℝ, ContDiffOn ℝ
∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, R.normalizedDefect hσ t=t^3*g t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_derivative`,
`«2610.05164v2».Calibration.ReferenceData.normalizedDefectRHS_zero` with the arguments shown in
the proof.
-/
theorem normalizedDefect_first_zero : derivWithin (R.normalizedDefect hσ) (Icc (0:ℝ) 1) 0=0 :=
  ((R.normalizedDefect_derivative hσ (show (0:ℝ) ∈ Icc 0 1 by norm_num)).derivWithin
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num))).trans (R.normalizedDefectRHS_zero hσ)
/--
Exact identity `iteratedDerivWithin 2 (R.normalizedDefect hσ) (Icc (0:ℝ) 1) 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_cubic_quotient` uses this
identity to construct witnesses satisfying `∃ g : ℝ → ℝ, ContDiffOn ℝ
∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, R.normalizedDefect hσ t=t^3*g t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedVelocity_smooth`,
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_derivative`,
`«2610.05164v2».Calibration.ReferenceData.normalizedDefectRHS_zero` with the arguments shown in
the proof.
-/
theorem normalizedDefect_second_zero :
    iteratedDerivWithin 2 (R.normalizedDefect hσ) (Icc (0:ℝ) 1) 0=0 := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedVelocity_smooth`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_derivative`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedDefectRHS_zero` with the arguments
  -- shown in the proof.
  have hp := (R.normalizedVelocity_smooth.differentiableOn
    (by simp) 0 (show (0:ℝ) ∈ Icc 0 1 by norm_num)).hasDerivWithinAt
  have hδ := R.normalizedDefect_derivative hσ (show (0:ℝ) ∈ Icc 0 1 by norm_num)
  rw [R.normalizedDefectRHS_zero hσ] at hδ
  have ht := hasDerivWithinAt_id (0:ℝ) (Icc (0:ℝ) 1)
  have hb := (((ht.pow 6).const_mul (1+σ)).sub
    ((((ht.pow 3).const_mul σ).const_add 1).const_mul 2 |>.mul hδ)).add
      ((hδ.pow 2).const_mul σ)
  have hprod := hp.mul hb
  have hzero : HasDerivWithinAt (R.normalizedDefectRHS hσ) 0 (Icc (0:ℝ) 1) 0 := by
    convert! hprod using 1
    simp [R.normalizedDefect_zero hσ]
  have heq : EqOn (derivWithin (R.normalizedDefect hσ) (Icc (0:ℝ) 1))
      (R.normalizedDefectRHS hσ) (Icc (0:ℝ) 1) := by
    intro t ht
    exact (R.normalizedDefect_derivative hσ ht).derivWithin
      (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht)
  rw [show (2:ℕ)=1+1 by rfl,iteratedDerivWithin_succ,iteratedDerivWithin_one]
  rw [derivWithin_congr heq (heq (by norm_num : (0:ℝ) ∈ Icc 0 1))]
  exact hzero.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num))

/--
Constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀
t ∈ Icc (0:ℝ) 1, R.normalizedDefect hσ t=t^3*g t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient` uses this identity in
the displayed construction of `normalizedDefectQuotient`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.smooth_cubic_quotient`,
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_smooth`,
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_zero` with the arguments shown in
the proof.
-/
theorem normalizedDefect_cubic_quotient :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧
      ∀ t ∈ Icc (0:ℝ) 1, R.normalizedDefect hσ t=t^3*g t :=
  smooth_cubic_quotient (by norm_num : (0:ℝ)<1) (R.normalizedDefect_smooth hσ)
    (R.normalizedDefect_zero hσ) (R.normalizedDefect_first_zero hσ)
    (R.normalizedDefect_second_zero hσ)

 /--
Constructs witnesses with the exact properties `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1,
0≤R.normalizedDefect hσ t ∧ R.normalizedDefect hσ t≤C*t^7`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_zero` uses this bound
to establish the identity `R.normalizedDefectQuotient hσ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.defect_order_seven`,
`«2610.05164v2».Calibration.ReferenceData.normalizedVelocity_smooth`,
`«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_positive` with the arguments shown in
the proof.
-/
theorem normalizedDefect_order_seven :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1,
      0≤R.normalizedDefect hσ t ∧ R.normalizedDefect hσ t≤C*t^7 := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.defect_order_seven`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedVelocity_smooth`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_positive` with the arguments
  -- shown in the proof.
  apply defect_order_seven hσ.le R.normalizedVelocity_smooth.continuousOn
    (fun t ht => div_nonneg (by norm_num) (R.normalizedSpeed_positive ht).le)
    (R.normalizedDefect_smooth hσ).continuousOn (R.normalizedDefect_zero hσ)
    (fun t ht => R.normalizedDefect_bounds hσ ht)
  intro t ht
  exact (R.normalizedDefect_derivative hσ ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end
end «2610.05164v2».Calibration.ReferenceData
