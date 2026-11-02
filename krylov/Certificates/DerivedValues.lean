import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
Article: main_krylov, apC:prop:digits, thm:value, cor:threshold and prop:HS.
Use: propagate rational crossing brackets to every numerical value printed
in the mathematical part of the article. These lemmas are pure ordered-field
arithmetic; they take crossing enclosures, not numerical solver output.
Source: monotonicity of the positive square root and reciprocal. Every bound
below is proved in the kernel by rational arithmetic. The final strict
half-unit intervals give the agreed five significant decimal digits.
-/

namespace krylov.Certificates
noncomputable section

/-- A half-gamma crossing in the certified decimal window gives a much
narrower interval than is needed to print `a = 1.3287` to five significant
digits. -/
theorem half_sqrt_bounds {s : ℝ}
    (hl : (176535 / 100000 : ℝ) < s) (hu : s < 176536 / 100000) :
    (132866 / 100000 : ℝ) < Real.sqrt s ∧ Real.sqrt s < 132867 / 100000 := by
  constructor
  · apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 132866 / 100000)).mpr
    linarith
  · apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 132867 / 100000)).mpr
    linarith

/-- The reciprocal is both the initial optimizing density and the atom at
zero of the actual principal spectral measure, by the analytic theorems. -/
theorem half_inverse_bounds {s : ℝ}
    (hl : (176535 / 100000 : ℝ) < s) (hu : s < 176536 / 100000) :
    (566455 / 1000000 : ℝ) < s⁻¹ ∧ s⁻¹ < 566465 / 1000000 := by
  have hs : 0 < s := lt_trans (by norm_num) hl
  constructor
  · rw [← one_div]
    apply (lt_div_iff₀ hs).mpr
    nlinarith
  · rw [← one_div]
    apply (div_lt_iff₀ hs).mpr
    nlinarith

/-- Five significant digits of the sharp FC tolerance coefficient `2/a`.
The root is positive, so multiplication by it preserves strict inequalities. -/
theorem half_tolerance_bounds {s : ℝ}
    (hl : (176535 / 100000 : ℝ) < s) (hu : s < 176536 / 100000) :
    (150525 / 100000 : ℝ) < 2 / Real.sqrt s ∧
      2 / Real.sqrt s < 150535 / 100000 := by
  have hs : 0 < s := lt_trans (by norm_num) hl
  have hr := half_sqrt_bounds hl hu
  constructor
  · apply (lt_div_iff₀ (Real.sqrt_pos.mpr hs)).mpr
    nlinarith [hr.2]
  · apply (div_lt_iff₀ (Real.sqrt_pos.mpr hs)).mpr
    nlinarith [hr.1]

/-- Five significant digits of the endpoint optimal continuum reward. -/
theorem endpoint_reward_bounds {t : ℝ}
    (hl : (264667 / 100000 : ℝ) < t) (hu : t < 264668 / 100000) :
    (813425 / 1000000 : ℝ) < Real.sqrt t / 2 ∧
      Real.sqrt t / 2 < 813435 / 1000000 := by
  constructor
  · have h : (162685 / 100000 : ℝ) < Real.sqrt t := by
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 162685 / 100000)).mpr
      linarith
    linarith
  · have h : Real.sqrt t < (162687 / 100000 : ℝ) := by
      apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 162687 / 100000)).mpr
      linarith
    linarith

/-- Five significant digits of the physical Hilbert--Schmidt quarter-power
coefficient. The analytic scaling theorem gives precisely `sqrt(a₁/4)`,
with `a₁ = sqrt(t)/2`; this is `sqrt(sqrt(t)/8)`. -/
theorem endpoint_hs_bounds {t : ℝ}
    (hl : (264667 / 100000 : ℝ) < t) (hu : t < 264668 / 100000) :
    (450945 / 1000000 : ℝ) < Real.sqrt (Real.sqrt t / 8) ∧
      Real.sqrt (Real.sqrt t / 8) < 450955 / 1000000 := by
  have ht := endpoint_reward_bounds hl hu
  constructor
  · apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 450945 / 1000000)).mpr
    linarith [ht.1]
  · apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 450955 / 1000000)).mpr
    linarith [ht.2]

/-- All agreed rounded mathematical decimals, expressed as strict
half-last-unit enclosures. Strictness excludes rounding ties. No precision
beyond these five significant digits is asserted. -/
theorem five_significant_derived_values {s t : ℝ}
    (hsl : (176535 / 100000 : ℝ) < s) (hsu : s < 176536 / 100000)
    (htl : (264667 / 100000 : ℝ) < t) (htu : t < 264668 / 100000) :
    |s - 17654 / 10000| < 1 / 20000 ∧
    |t - 26467 / 10000| < 1 / 20000 ∧
    |Real.sqrt s - 13287 / 10000| < 1 / 20000 ∧
    |s⁻¹ - 56646 / 100000| < 1 / 200000 ∧
    |2 / Real.sqrt s - 15053 / 10000| < 1 / 20000 ∧
    |Real.sqrt t / 2 - 81343 / 100000| < 1 / 200000 ∧
    |Real.sqrt (Real.sqrt t / 8) - 45095 / 100000| < 1 / 200000 := by
  have ha := half_sqrt_bounds hsl hsu
  have hi := half_inverse_bounds hsl hsu
  have hc := half_tolerance_bounds hsl hsu
  have he := endpoint_reward_bounds htl htu
  have hh := endpoint_hs_bounds htl htu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> linarith

end
end krylov.Certificates
