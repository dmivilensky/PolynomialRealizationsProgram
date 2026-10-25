import polyak.Boundary.P5.System
import polyak.Boundary.Tail
import polyak.Spiral.Cycle
import Mathlib.Analysis.Convex.Deriv

/-!
Article: Lemma p5tail, elementary uniform hyperbolic estimates.
Use: the growing radial term dominates n²h and the value term stays below 7.7nh
when nt≤3. No positive lower bound on h is imposed.
-/

noncomputable section
namespace polyak.Boundary.P5
open Set Spectral

/-- Article: the exact numerical bounds used in the two cases of the tail proof. -/
theorem exp_three_bounds : (20 : ℝ) < Real.exp 3 ∧ Real.exp 3 < 21 := by
  have hl : (2718/1000 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hu : Real.exp 1 < (2719/1000 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hl3 : (2718/1000 : ℝ)^3 < Real.exp 1^3 := by gcongr
  have hu3 : Real.exp 1^3 < (2719/1000 : ℝ)^3 := by gcongr
  have he := Real.exp_nat_mul (1 : ℝ) 3
  norm_num only [Nat.cast_ofNat,mul_one] at he
  rw [he]
  constructor <;> norm_num at * <;> linarith

/-- Article: cosh3>10 and sinh3<21/2, proved from exact exponential bounds. -/
theorem hyperbolic_three_bounds : (10 : ℝ) < Real.cosh 3 ∧ Real.sinh 3 < 21/2 := by
  have he := exp_three_bounds
  have hn := Real.exp_pos (-3)
  constructor
  · rw [Real.cosh_eq]
    linarith
  · rw [Real.sinh_eq]
    linarith

/-- Article: convexity of sinh on the nonnegative half-line. -/
theorem sinh_convexOn_nonneg : ConvexOn ℝ (Ici 0) Real.sinh := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0)
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn
  intro x hx y hy hxy
  simp only [Real.deriv_sinh]
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (interior_subset hx),abs_of_nonneg (interior_subset hy)]
  exact hxy

/-- Article: the convex secant bound sinh x≤(x/3)sinh3 on [0,3]. -/
theorem sinh_le_three_secant {x : ℝ} (hx : 0 ≤ x) (hx3 : x ≤ 3) :
    Real.sinh x ≤ x/3*Real.sinh 3 := by
  have h := sinh_convexOn_nonneg.2 (show (0 : ℝ) ∈ Ici 0 by simp)
    (show (3 : ℝ) ∈ Ici 0 by norm_num) (show 0 ≤ 1-x/3 by linarith)
    (show 0 ≤ x/3 by positivity) (show 1-x/3+x/3=1 by ring)
  simpa only [smul_eq_mul,mul_zero,zero_add,div_mul_cancel₀ _ (by norm_num : (3 : ℝ)≠0),
    Real.sinh_zero,mul_zero,zero_add] using h

/-- Article: the first differences of cosh(nt) dominate (2n+1)(cosh t−1). -/
theorem cosh_nat_difference_lower (t : ℝ) (n : ℕ) :
    (2*n+1)*(Real.cosh t-1) ≤ Real.cosh ((n+1)*t)-Real.cosh (n*t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := Spiral.chebT_recurrence (Real.cosh t) n
    simp only [chebT_cosh] at hr
    have hc := Real.one_le_cosh ((n+1)*t)
    have ht := Real.one_le_cosh t
    have hp := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hc)
    push_cast at hr ⊢
    rw [show (n : ℝ)+1+1=n+2 by ring]
    nlinarith

/-- Article: cosh(nt)−1≥n²h whenever cosh t=1+h. -/
theorem cosh_nat_lower (t : ℝ) (n : ℕ) :
    (n : ℝ)^2*(Real.cosh t-1) ≤ Real.cosh (n*t)-1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd := cosh_nat_difference_lower t n
    push_cast at hd ⊢
    nlinarith

/-- Article: Uₙ₋₁(cosh t)≤(7/2)n uniformly for 0<nt≤3. -/
theorem lagDenominator_le_three {t : ℝ} (ht : 0 < t) (n : ℕ) (hn : 1 ≤ n)
    (hnt : n*t ≤ 3) :
    lagDenominator (Real.cosh t) n ≤ (7/2 : ℝ)*n := by
  have hnt0 : 0 ≤ (n : ℝ)*t := mul_nonneg (Nat.cast_nonneg _) ht.le
  have hs := sinh_le_three_secant hnt0 hnt
  have htsh := Real.self_le_sinh_iff.mpr ht.le
  have hden := lagDenominator_pos (Real.one_le_cosh t) n hn
  have hid := lagDenominator_mul_sinh t n hn
  have hh := mul_le_mul_of_nonneg_left htsh hden.le
  have hsh3 := hyperbolic_three_bounds.2
  have hm := mul_le_mul_of_nonneg_left hsh3.le (show 0 ≤ (n : ℝ)*t/3 by positivity)
  have hh' : lagDenominator (Real.cosh t) n*t ≤ (7/2 : ℝ)*n*t := by
    nlinarith
  nlinarith

end polyak.Boundary.P5
