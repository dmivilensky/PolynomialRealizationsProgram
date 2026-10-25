import polyak.Boundary.P2.Moments
import polyak.Boundary.P2.Dual
import polyak.Boundary.P2.Chebyshev
import polyak.Boundary.Tail
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
Article: Theorem p2arc(v) and the entire infinite tail m≥10.
Use: the source decimal constants are exact rationals; all raw lags are covered.
-/

namespace polyak.Boundary.P2
noncomputable section
open Spectral

/-- Article: a P₂ exponent with the prescribed cosh is nonzero. -/
theorem exponent_ne_zero {z t : ℝ} (hz : z∈parameterInterval) (ht : Real.cosh t=G z) : t≠0 := by
  intro he
  rw [he,Real.cosh_zero] at ht
  have hg := one_lt_G hz
  linarith

/-- Article: the actual averaged minimizer constraint has a strict gap larger than 0.28. -/
theorem minimizer_gap {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z)
    (ht : Real.cosh t=G z) :
    (7/25 : ℝ) < meanG (spectrum z hz h1) (u z)-|d z/Real.sinh t| := by
  rw [meanG_spectrum]
  have hd := d_positive_positive z hz
  have hg := gap_lower_positive z hz
  have hcert := gap_square_positive z hz
  have hs : 0 < |Real.sinh t| := abs_pos.mpr (Real.sinh_ne_zero.mpr (exponent_ne_zero hz ht))
  have hsq : |Real.sinh t|^2=G z^2-1 := by rw [sq_abs,Real.sinh_sq,ht]
  let Q := (meanGap z-7/25)*|Real.sinh t|
  have hQ : 0 < Q := mul_pos hg hs
  have hQsq : d z^2<Q^2 := by
    dsimp [Q]
    rw [mul_pow,hsq]
    linarith
  have hdQ : d z<Q := (sq_lt_sq₀ hd.le hQ.le).mp hQsq
  have hdiv : d z/|Real.sinh t|<meanGap z-7/25 := by
    apply (div_lt_iff₀ hs).mpr
    exact hdQ
  rw [abs_div,abs_of_pos hd]
  linarith

/-- Article: the exact Chebyshev numerical inequality used at the first unverified lag. -/
theorem tenth_chebyshev_lower : (4369/1000 : ℝ)<chebT 10 (10233/10000) := by
  norm_num [chebT,Tpoly10]

/-- Article: every cosh(nt), n≥10, exceeds the same exact tail constant. -/
theorem cosh_lag_lower {z t : ℝ} (hz : z∈parameterInterval) (ht : Real.cosh t=G z)
    (n : ℕ) (hn : 10 ≤ n) : (4369/1000 : ℝ)<Real.cosh (n*t) := by
  let a := Real.arcosh (10233/10000)
  have hga : (1 : ℝ) ≤ 10233/10000 := by norm_num
  have habs : |a| ≤ |t| := by
    apply Real.cosh_le_cosh.mp
    dsimp [a]
    rw [Real.cosh_arcosh hga,ht]
    have hg := G_lower_positive z hz
    linarith
  have hargs : |(10 : ℝ)*a| ≤ |(n : ℝ)*t| := by
    simp only [abs_mul]
    have h10 : |(10 : ℝ)|=10 := abs_of_nonneg (by norm_num)
    have hnabs : |(n : ℝ)|=n := abs_of_nonneg (Nat.cast_nonneg n)
    rw [h10,hnabs]
    calc
      10*|a| ≤ 10*|t| := mul_le_mul_of_nonneg_left habs (by norm_num)
      _ ≤ (n : ℝ)*|t| := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (abs_nonneg t)
  have hcosh := Real.cosh_le_cosh.mpr hargs
  have hten : Real.cosh (10*a)=chebT 10 (10233/10000) := by
    have h := chebT_cosh 10 a
    norm_num only [Nat.cast_ofNat] at h
    rw [←h]
    dsimp [a]
    rw [Real.cosh_arcosh hga]
  rw [hten] at hcosh
  exact tenth_chebyshev_lower.trans_le hcosh

/-- Article: every actual raw lag n≥10 has margin greater than 0.17, for either exponent sign. -/
theorem infinite_tail_positive {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z)
    (ht : Real.cosh t=G z) (n : ℕ) (hn : 10 ≤ n) :
    (17/100 : ℝ)<meanA (spectrum z hz h1) (u z) t n-meanB (spectrum z hz h1) (u z) n+
      (d z/Real.sinh t)*Real.sinh (n*t) ∧
    (17/100 : ℝ)<meanA (spectrum z hz h1) (u z) t n+meanB (spectrum z hz h1) (u z) n-
      (d z/Real.sinh t)*Real.sinh (n*t) := by
  have hgap := minimizer_gap hz h1 ht
  have hcosh := cosh_lag_lower hz ht n hn
  have hupper : meanG (spectrum z hz h1) (u z)+2*u z^2 < 21/20 := by
    rw [meanG_spectrum]
    have h := tail_gap_positive z hz
    linarith
  have hprod : (7/25 : ℝ)*(4369/1000) <
      (meanG (spectrum z hz h1) (u z)-|d z/Real.sinh t|)*Real.cosh (n*t) := by
    calc
      (7/25 : ℝ)*(4369/1000) < (7/25 : ℝ)*Real.cosh (n*t) :=
        mul_lt_mul_of_pos_left hcosh (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right hgap (Real.cosh_pos _)
  have htail := Boundary.raw_lag_tail_both (spectrum z hz h1) (u z) (d z/Real.sinh t) t n (by omega)
  constructor <;> nlinarith [htail.1,htail.2]

end
end polyak.Boundary.P2
