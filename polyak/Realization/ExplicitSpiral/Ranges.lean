import polyak.Realization.ExplicitSpiral.Coordinates
import polyak.Spiral.Threshold

/-!
Article: the covering intervals for the initialized-spiral sign checks.
Use: the small-q estimate and the three compact radial regions cover every
admissible condition number, with exact rational endpoints and overlap.
Proof: monotonicity and explicit signs of the independently defined master polynomial.
-/

namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Spiral

/-- Article: the positive radial root is strictly beyond q. -/
theorem root_gt_q {r q : ℝ} (hr : 0<r) (_hq : 0<q)
    (hroot : spiralPolynomial r q=0) : q<r := by
  by_contra hh
  have hn := spiralPolynomial_neg_of_le hr (le_of_not_gt hh)
  rw [hroot] at hn
  linarith

/-- Article: the small-q case has every positive wave amplitude at most 1/2. -/
theorem root_lt_half {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq5 : q≤1/5)
    (hroot : spiralPolynomial r q=0) : r<1/2 := by
  have hq1 : q<1 := by linarith
  have he : 0<spiralPolynomial (1/2) q := by
    have hbase : 0<spiralPolynomial (1/2) (1/5) := by norm_num [spiralPolynomial]
    rcases lt_or_eq_of_le hq5 with h | h
    · exact hbase.trans (spiralPolynomial_parameter_lt (by norm_num) hq h)
    · rwa [h]
  by_contra hn
  have hh := (spiralPolynomial_strictMonoOn hq hq1).monotoneOn
    (show (1/2 : ℝ)∈Set.Ici q by exact le_trans hq5 (by norm_num))
    (root_gt_q hr hq hroot).le (le_of_not_gt hn)
  rw [hroot] at hh
  linarith

/-- Article: the compact sign-table region begins before every root with q≥1/5. -/
theorem root_gt_lower {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hq5 : 1/5≤q) (hroot : spiralPolynomial r q=0) : 33/100<r := by
  by_cases hq33 : 33/100≤q
  · exact hq33.trans_lt (root_gt_q hr hq hroot)
  · have hq33' : q<33/100 := lt_of_not_ge hq33
    have he : spiralPolynomial (33/100) q<0 := by
      have hbase : spiralPolynomial (33/100) (1/5)<0 := by norm_num [spiralPolynomial]
      rcases lt_or_eq_of_le hq5 with h | h
      · exact (spiralPolynomial_parameter_lt (by norm_num) (by norm_num) h).trans hbase
      · rwa [← h]
    by_contra hn
    have hh := (spiralPolynomial_strictMonoOn hq hq1).monotoneOn
      (root_gt_q hr hq hroot).le hq33'.le (le_of_not_gt hn)
    rw [hroot] at hh
    linarith

/-- Article: the universal radial endpoint is below the exact rational cap 1.713. -/
theorem root_lt_upper {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hroot : spiralPolynomial r q=0) : r<1713/1000 := by
  have he : 0<spiralPolynomial (1713/1000) q := by
    have hbase : 0<spiralPolynomial (1713/1000) 1 := by norm_num [spiralPolynomial]
    exact hbase.trans (spiralPolynomial_parameter_lt (by norm_num) hq hq1)
  by_contra hn
  have hh := (spiralPolynomial_strictMonoOn hq hq1).monotoneOn
    (show (1713/1000 : ℝ)∈Set.Ici q from (by change q≤1713/1000; linarith))
    (root_gt_q hr hq hroot).le (le_of_not_gt hn)
  rw [hroot] at hh
  linarith

/-- Article: the large-q initial-gradient bound uses the exact inequality ρ<2q. -/
theorem root_lt_two_q {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hq5 : 1/5≤q) (hroot : spiralPolynomial r q=0) : r<2*q := by
  have hpoly : 0<8*q-4*q^2-1 := by
    have h := mul_nonneg (sub_nonneg.mpr hq5) (sub_nonneg.mpr hq1.le)
    nlinarith
  have he : 0<spiralPolynomial (2*q) q := by
    have hid : spiralPolynomial (2*q) q=q^2*(8*q-4*q^2-1) := by unfold spiralPolynomial; ring
    rw [hid]
    positivity
  by_contra hn
  have hh := (spiralPolynomial_strictMonoOn hq hq1).monotoneOn
    (show 2*q∈Set.Ici q from (by change q≤2*q; linarith))
    (root_gt_q hr hq hroot).le (le_of_not_gt hn)
  rw [hroot] at hh
  linarith

/-- Article: the exact spiral minimizer gap has the uniform upper bound 1/2. -/
theorem source_gap_half (r : ℝ) : Source.gap r=1/2-(r-1)^4/(2*(r^2+1)^2) := by
  unfold Source.gap
  field_simp
  ring

end
end polyak.Realization.ExplicitSpiral
