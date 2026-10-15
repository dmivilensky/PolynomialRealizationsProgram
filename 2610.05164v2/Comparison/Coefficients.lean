import «2610.05164v2».Calibration.Tangent

/-!
Article: 2610.05164v2, Theorem 3.4.
The signed comparison coefficients and their sharp triangle bounds.
Use: `«2610.05164v2».Comparison.traceCoefficient_bounds` feeds
`«2610.05164v2».Calibration.Data.comparisonA0_bound` (comparison A0 bound).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_trace_comparison` — 2610.05164v2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison
noncomputable section
open «2610.05164v2».Calibration

/--
Defines `determinantCoefficient` of type `ℝ` by `-(s*Q q+κ*r*R)/(d*(2+r+R))`.

Use: `«2610.05164v2».Comparison.determinantCoefficient_bounds` uses this definition to
establish membership in the specified domain/enclosure: `determinantCoefficient κ s q d r R ∈
Set.Icc (-s*Q q/(2*d)) 0`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantCoefficient (κ s q d r R : ℝ) : ℝ := -(s*Q q+κ*r*R)/(d*(2+r+R))
/--
Defines `traceCoefficient` of type `ℝ` by `κ*(2*r*R-Q q*(r+R))/(2*d)`.

Use: `«2610.05164v2».Comparison.traceCoefficient_bounds` uses this definition to establish
membership in the specified domain/enclosure: `traceCoefficient κ q d r R ∈ Set.Icc (-κ*Q q/d)
0`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def traceCoefficient (κ q d r R : ℝ) : ℝ := κ*(2*r*R-Q q*(r+R))/(2*d)

/--
The stated quantitative bound `2*κ*r*R ≤ s*Q q*(r+R)`.

Use: `«2610.05164v2».Comparison.determinantCoefficient_bounds` uses this bound to establish
membership in the specified domain/enclosure: `determinantCoefficient κ s q d r R ∈ Set.Icc
(-s*Q q/(2*d)) 0`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem product_triangle {κ s q r R : ℝ} (hκ : 0 < κ) (_hs : 0 ≤ s)
    (hq : q ∈ Set.Icc (0:ℝ) 2) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hrb : r ≤ s/κ*q) (hRb : R ≤ s/κ*(2-q)) :
    2*κ*r*R ≤ s*Q q*(r+R) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have h1 : κ*r ≤ s*q := by simpa only [mul_comm] using (le_div_iff₀ hκ).mp (by simpa only [div_mul_eq_mul_div] using hrb)
  have h2 : κ*R ≤ s*(2-q) := by simpa only [mul_comm] using (le_div_iff₀ hκ).mp (by simpa only [div_mul_eq_mul_div] using hRb)
  have ha := mul_nonneg (sub_nonneg.mpr h1) (mul_nonneg (sub_nonneg.mpr hq.2) hR)
  have hb := mul_nonneg (sub_nonneg.mpr h2) (mul_nonneg hq.1 hr)
  unfold Q
  nlinarith

/--
Membership in the specified domain/enclosure: `determinantCoefficient κ s q d r R ∈ Set.Icc
(-s*Q q/(2*d)) 0`.

Use: `«2610.05164v2».Calibration.Data.comparisonA_bound` uses this assertion to establish the
stated quantitative bound `‖C.comparisonA hκ s q r‖ ≤ s/(4*C.b)*C.amplitude κ q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.product_triangle`,
`«2610.05164v2».Calibration.Q_nonneg` with the arguments shown in the proof.
-/
theorem determinantCoefficient_bounds {κ s q d r R : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hq : q ∈ Set.Icc (0:ℝ) 2) (hd : 0 < d) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hrb : r ≤ s/κ*q) (hRb : R ≤ s/κ*(2-q)) :
    determinantCoefficient κ s q d r R ∈ Set.Icc (-s*Q q/(2*d)) 0 := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.product_triangle`,
  -- `«2610.05164v2».Calibration.Q_nonneg` with the arguments shown in the proof.
  have hp := product_triangle hκ hs hq hr hR hrb hRb
  have hQ := Q_nonneg hq
  have hden : 0 < d*(2+r+R) := mul_pos hd (by linarith)
  unfold determinantCoefficient
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0<2*d) hden).2
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hp)]
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
      (add_nonneg (mul_nonneg hs hQ) (mul_nonneg (mul_nonneg hκ.le hr) hR))) hden.le

/--
Membership in the specified domain/enclosure: `traceCoefficient κ q d r R ∈ Set.Icc (-κ*Q q/d)
0`.

Use: `«2610.05164v2».Calibration.Data.comparisonA0_bound` uses this assertion to establish the
stated quantitative bound `‖C.comparisonA0 hκ q r‖ ≤ κ/(2*C.b)*C.amplitude κ q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.product_triangle`,
`«2610.05164v2».Calibration.Q_nonneg` with the arguments shown in the proof.
-/
theorem traceCoefficient_bounds {κ q d r R : ℝ} (hκ : 0 < κ)
    (hq : q ∈ Set.Icc (0:ℝ) 2) (hd : 0 < d)
    (hr : r ∈ Set.Icc (0:ℝ) q) (hR : R ∈ Set.Icc (0:ℝ) (2-q)) :
    traceCoefficient κ q d r R ∈ Set.Icc (-κ*Q q/d) 0 := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.product_triangle`,
  -- `«2610.05164v2».Calibration.Q_nonneg` with the arguments shown in the proof.
  have hp := product_triangle hκ (show 0 ≤ κ from hκ.le) hq hr.1 hR.1
    (by simpa only [div_self hκ.ne',one_mul] using hr.2)
    (by simpa only [div_self hκ.ne',one_mul] using hR.2)
  have hQ := Q_nonneg hq
  have hsum : r+R ≤ 2 := by linarith [hr.2,hR.2]
  unfold traceCoefficient
  constructor
  · apply (div_le_div_iff₀ hd (by positivity : 0<2*d)).2
    have hp0 := mul_nonneg hr.1 hR.1
    have hq0 := mul_nonneg hQ (sub_nonneg.mpr hsum)
    nlinarith [mul_nonneg (mul_nonneg hκ.le hd.le) (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hp0) hq0)]
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have he : 2*r*R ≤ Q q*(r+R) := (mul_le_mul_iff_right₀ hκ).mp (by nlinarith [hp])
    exact mul_nonpos_of_nonneg_of_nonpos hκ.le (sub_nonpos.mpr he)

/--
The precise assertion is `(-(r*R+s*ν^2)/(d*(2+r+R)))*(κ*n^2-Q q)+ (s*n^2-2*r-r^2)/(2+r+R)=
-r+determinantCoefficient κ s q d r R*(n^2-ν^2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.4.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem determinant_drift {κ d : ℝ} (hd : d ≠ 0) (ν s q r R n : ℝ)
    (hD : d=κ*ν^2-Q q) (hden : 2+r+R ≠ 0) :
    (-(r*R+s*ν^2)/(d*(2+r+R)))*(κ*n^2-Q q)+
      (s*n^2-2*r-r^2)/(2+r+R)=
        -r+determinantCoefficient κ s q d r R*(n^2-ν^2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  unfold determinantCoefficient
  field_simp
  rw [hD]
  unfold Q
  ring

/--
The precise assertion is `(2*r*R-κ*ν^2*(r+R))/(2*d)*(κ*n^2-Q q)+ (r+R)/2*(κ*n^2-2*r)=
-r^2+traceCoefficient κ q d r R*(n^2-ν^2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.4.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem trace_drift {κ d : ℝ} (hd : d ≠ 0) (ν q r R n : ℝ)
    (hD : d=κ*ν^2-Q q) :
    (2*r*R-κ*ν^2*(r+R))/(2*d)*(κ*n^2-Q q)+
      (r+R)/2*(κ*n^2-2*r)=
        -r^2+traceCoefficient κ q d r R*(n^2-ν^2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  unfold traceCoefficient
  field_simp
  rw [hD]
  unfold Q
  ring

end
end «2610.05164v2».Comparison
