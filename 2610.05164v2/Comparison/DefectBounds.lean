import «2610.05164v2».Comparison.EndpointDefect

/-!
Article: 2610.05164v2, Theorem 3.6.
Lemma 13's uniform endpoint defects for the actual comparison filters.
Use: `«2610.05164v2».Calibration.Data.defectConstant_continuousOn` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_joint_continuous` (defect
Quotient joint continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Calibration «2610.05164v2».Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data) {κ s : ℝ} (hκ : 0 < κ)

/--
Defines `leftDefect` of type `ℝ` by `q-κ/s*C.leftFilter hκ s q`.

Use: `«2610.05164v2».Calibration.Data.leftDefect_bounds` uses this definition to establish
membership in the specified domain/enclosure: `C.leftDefect hκ s q ∈ Icc (0:ℝ) q`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def leftDefect (s q : ℝ) : ℝ := q-κ/s*C.leftFilter hκ s q
/--
Defines `leftLinearDefect` of type `ℝ` by `q-C.leftLinear hκ q`.

Use: `«2610.05164v2».Calibration.Data.leftLinearDefect_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt (C.leftLinearDefect hκ)
((q^2-2*C.leftLinearDefect hκ q)/C.speed κ q) q`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def leftLinearDefect (q : ℝ) : ℝ := q-C.leftLinear hκ q

/--
Membership in the specified domain/enclosure: `C.leftDefect hκ s q ∈ Icc (0:ℝ) q`.

Use: `«2610.05164v2».Calibration.Data.comparison_defects_bound_compact` uses this assertion to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ
∈ K → ∀ q ∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧ C.leftLinearDefect hκ
q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ))`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem leftDefect_bounds (hs : 0 < s) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    C.leftDefect hκ s q ∈ Icc (0:ℝ) q := by
  have hb := C.leftFilter_bounds hκ hs.le hq
  have he : κ/s*(s/κ*q)=q := by field_simp
  have h := mul_le_mul_of_nonneg_left hb.2 (div_nonneg hκ.le hs.le)
  exact ⟨by dsimp [leftDefect]; linarith,
    sub_le_self _ (mul_nonneg (div_nonneg hκ.le hs.le) hb.1)⟩

/--
Membership in the specified domain/enclosure: `C.leftLinearDefect hκ q ∈ Icc (0:ℝ) q`.

Use: `«2610.05164v2».Calibration.Data.comparison_defects_bound_compact` uses this assertion to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ
∈ K → ∀ q ∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧ C.leftLinearDefect hκ
q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ))`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftLinear_bounds` with
the arguments shown in the proof.
-/
theorem leftLinearDefect_bounds {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    C.leftLinearDefect hκ q ∈ Icc (0:ℝ) q :=
  ⟨sub_nonneg.mpr (C.leftLinear_bounds hκ hq).2,
    sub_le_self _ (C.leftLinear_bounds hκ hq).1⟩

/--
The actual derivative at the stated point: `HasDerivAt (C.leftDefect hκ s)
(((1+s/κ)*q^2-2*(1+(s/κ)*q)*C.leftDefect hκ s q+ (s/κ)*(C.leftDefect hκ s q)^2)/C.speed κ q)
q`.

Use: `«2610.05164v2».Calibration.Data.leftDefect_endpoint_bound` uses this derivative formula
to prove the bound `C.leftDefect hκ s q ≤ C.defectConstant κ
s*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem leftDefect_derivative (hs : 0 < s) {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (C.leftDefect hκ s)
      (((1+s/κ)*q^2-2*(1+(s/κ)*q)*C.leftDefect hκ s q+
        (s/κ)*(C.leftDefect hκ s q)^2)/C.speed κ q) q := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  convert! (hasDerivAt_id q).sub ((C.leftFilter_derivative hκ hs.le hq).const_mul (κ/s)) using 1
  dsimp [leftDefect]
  field_simp [hκ.ne',hs.ne',(C.speed_positive hκ hq).ne']
  unfold speed Q
  ring

/--
The actual derivative at the stated point: `HasDerivAt (C.leftLinearDefect hκ)
((q^2-2*C.leftLinearDefect hκ q)/C.speed κ q) q`.

Use: `«2610.05164v2».Calibration.Data.leftLinearDefect_endpoint_bound` uses this derivative
formula to prove the bound `C.leftLinearDefect hκ q ≤ C.defectConstant
κ 0*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem leftLinearDefect_derivative {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (C.leftLinearDefect hκ)
      ((q^2-2*C.leftLinearDefect hκ q)/C.speed κ q) q := by
  convert! (hasDerivAt_id q).sub (C.leftLinear_derivative hκ hq) using 1
  dsimp [leftLinearDefect]
  field_simp [(C.speed_positive hκ hq).ne']
  unfold speed Q
  ring

include hκ in
/--
The stated quantitative bound `0 ≤ C.reciprocalCoefficient κ`.

Use: `«2610.05164v2».Calibration.Data.comparison_defects_bound_compact` uses this bound to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ
∈ K → ∀ q ∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧ C.leftLinearDefect hκ
q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ))`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem reciprocalCoefficient_nonneg : 0 ≤ C.reciprocalCoefficient κ := by
  have hb := C.b_positive
  dsimp [reciprocalCoefficient]
  positivity

include hκ in
/--
The stated quantitative bound `(C.speed κ q)⁻¹ ≤ C.reciprocalCoefficient κ*q^(-(2/3:ℝ))`.

Use: `«2610.05164v2».Calibration.Data.leftDefect_endpoint_bound` uses this bound to establish
the stated quantitative bound `C.leftDefect hκ s q ≤ C.defectConstant κ s*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.reciprocal_bound`,
`«2610.05164v2».Calibration.Data.reciprocalCoefficient_nonneg` with the arguments shown in the
proof.
-/
theorem reciprocal_bound_left {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 1) :
    (C.speed κ q)⁻¹ ≤ C.reciprocalCoefficient κ*q^(-(2/3:ℝ)) := by
  have hQ : q ≤ Q q := by unfold Q; nlinarith [hq.1,hq.2]
  exact (C.reciprocal_bound hκ ⟨hq.1,by linarith [hq.2]⟩).trans
    (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hq.1 hQ (by norm_num))
      (C.reciprocalCoefficient_nonneg hκ))

/--
Defines `defectConstant` of type `ℝ` by `max (C.reciprocalCoefficient κ*(1+s/κ)*(3/7)) 2`.

Use: `«2610.05164v2».Calibration.Data.comparison_defects_bound_compact` uses this definition to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ
∈ K → ∀ q ∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧ C.leftLinearDefect hκ
q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ))`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def defectConstant (κ s : ℝ) : ℝ := max (C.reciprocalCoefficient κ*(1+s/κ)*(3/7)) 2

/--
The stated quantitative bound `C.leftDefect hκ s q ≤ C.defectConstant κ s*q^(7/3:ℝ)`.

Use: `«2610.05164v2».Calibration.Data.comparison_defects_bound_compact` uses this bound to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ
∈ K → ∀ q ∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧ C.leftLinearDefect hκ
q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ))`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.endpoint_defect_bound`,
`«2610.05164v2».Calibration.Data.reciprocalCoefficient_nonneg`,
`«2610.05164v2».Calibration.Data.leftFilter_ac` with the arguments shown in the proof.
-/
theorem leftDefect_endpoint_bound (hs : 0 < s) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    C.leftDefect hκ s q ≤ C.defectConstant κ s*q^(7/3:ℝ) := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.endpoint_defect_bound`,
  -- `«2610.05164v2».Calibration.Data.reciprocalCoefficient_nonneg`,
  -- `«2610.05164v2».Calibration.Data.leftFilter_ac` with the arguments shown in the proof.
  apply endpoint_defect_bound (div_nonneg hs.le hκ.le) (C.reciprocalCoefficient_nonneg hκ)
    (by
      convert! (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval (a := 0) (b := 2)).sub
        ((C.leftFilter_ac hκ hs.le).const_mul (κ/s)) using 1)
    (by simp only [leftDefect,C.leftFilter_zero hκ hs.le,mul_zero,sub_zero])
    (fun q hq => C.leftDefect_bounds hκ hs hq) (fun q hq => C.speed_positive hκ hq)
    (fun q hq => C.reciprocal_bound_left hκ hq) (fun q hq => C.leftDefect_derivative hκ hs hq) q hq

/--
The stated quantitative bound `C.leftLinearDefect hκ q ≤ C.defectConstant κ 0*q^(7/3:ℝ)`.

Use: `«2610.05164v2».Calibration.Data.comparison_defects_bound_compact` uses this bound to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ
∈ K → ∀ q ∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧ C.leftLinearDefect hκ
q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ))`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.endpoint_defect_bound`,
`«2610.05164v2».Calibration.Data.reciprocalCoefficient_nonneg`,
`«2610.05164v2».Calibration.Data.leftLinear_ac` with the arguments shown in the proof.
-/
theorem leftLinearDefect_endpoint_bound {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    C.leftLinearDefect hκ q ≤ C.defectConstant κ 0*q^(7/3:ℝ) := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.endpoint_defect_bound`,
  -- `«2610.05164v2».Calibration.Data.reciprocalCoefficient_nonneg`,
  -- `«2610.05164v2».Calibration.Data.leftLinear_ac` with the arguments shown in the proof.
  have h := endpoint_defect_bound (a := 0) (by norm_num) (C.reciprocalCoefficient_nonneg hκ)
    (by convert! (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval (a := 0) (b := 2)).sub (C.leftLinear_ac hκ) using 1)
    (by simp only [leftLinearDefect,C.leftLinear_zero hκ,sub_self])
    (fun q hq => C.leftLinearDefect_bounds hκ hq) (fun q hq => C.speed_positive hκ hq)
    (fun q hq => C.reciprocal_bound_left hκ hq)
    (fun q hq => by simpa only [add_zero,zero_mul,sub_zero,one_mul,mul_one] using C.leftLinearDefect_derivative hκ hq) q hq
  simpa only [defectConstant,zero_div,add_zero,one_mul,mul_one] using h

omit hκ in
/--
Continuity on the stated domain: `ContinuousOn (fun κ => C.defectConstant κ s) (Ioi (0:ℝ))`.

Use: `«2610.05164v2».Calibration.Data.comparison_defects_bound_compact` uses this continuity
result to construct witnesses satisfying `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ
: 0 < κ, κ ∈ K → ∀ q ∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧
C.leftLinearDefect hκ q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ))`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.reciprocalCoefficient_continuousAt` with the arguments shown
in the proof.
-/
theorem defectConstant_continuousOn (s : ℝ) : ContinuousOn (fun κ => C.defectConstant κ s) (Ioi (0:ℝ)) := by
  intro κ hκ
  apply ContinuousAt.continuousWithinAt
  dsimp [defectConstant]
  exact ((((C.reciprocalCoefficient_continuousAt hκ).mul
    (continuousAt_const.add (continuousAt_const.div continuousAt_id hκ.ne'))).mul
      continuousAt_const).max continuousAt_const)

omit hκ in
/--
One constant works for both filters on any compact positive parameter set.

Constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ ∈ K → ∀ q
∈ Icc (0:ℝ) 2, C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧ C.leftLinearDefect hκ q ∈ Icc
(0:ℝ) (A*q^(7/3:ℝ))`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.6.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.defectConstant_continuousOn`,
`«2610.05164v2».Calibration.Data.reciprocalCoefficient_nonneg`,
`«2610.05164v2».Calibration.Data.leftDefect_bounds` with the arguments shown in the proof.
-/
theorem comparison_defects_bound_compact (hs : 0 < s) {K : Set ℝ} (hK : IsCompact K)
    (hpos : ∀ κ ∈ K, 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ κ, ∀ hκ : 0 < κ, κ ∈ K → ∀ q ∈ Icc (0:ℝ) 2,
      C.leftDefect hκ s q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) ∧
      C.leftLinearDefect hκ q ∈ Icc (0:ℝ) (A*q^(7/3:ℝ)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.Data.defectConstant_continuousOn`,
  -- `«2610.05164v2».Calibration.Data.reciprocalCoefficient_nonneg`,
  -- `«2610.05164v2».Calibration.Data.leftDefect_bounds` with the arguments shown in the proof.
  obtain ⟨A,hA⟩ := hK.bddAbove_image ((C.defectConstant_continuousOn s).mono hpos)
  refine ⟨max A 2,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro κ hκ hk q hq
  have hcoef : C.defectConstant κ s ≤ max A 2 :=
    (hA (mem_image_of_mem _ hk)).trans (le_max_left _ _)
  have hpow : 0 ≤ q^(7/3:ℝ) := rpow_nonneg hq.1 _
  have hzero : C.defectConstant κ 0 ≤ C.defectConstant κ s := by
    apply max_le_max _ le_rfl
    rw [zero_div,add_zero,mul_one]
    have h := mul_nonneg (C.reciprocalCoefficient_nonneg hκ) (div_nonneg hs.le hκ.le)
    nlinarith
  refine ⟨⟨(C.leftDefect_bounds hκ hs hq).1,(C.leftDefect_endpoint_bound hκ hs hq).trans
    (mul_le_mul_of_nonneg_right hcoef hpow)⟩,
    ⟨(C.leftLinearDefect_bounds hκ hq).1,(C.leftLinearDefect_endpoint_bound hκ hq).trans
      (mul_le_mul_of_nonneg_right (hzero.trans hcoef) hpow)⟩⟩

end
end «2610.05164v2».Calibration.Data
