import polyak.Spectral.Compact
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
Article: Appendix B, Proposition threshold strip.
Use: confine every feasible Polyak spectrum to the stated strip, strictly off t=0.
Proof: combine lag one with the minimizer constraint. The simpler intermediate
bound |sinh v|≤exp(|t|)/2 follows from a cubic factorization at u=r/2;
it implies the article's strip and avoids a large expanded polynomial certificate.
-/

noncomputable section

open MeasureTheory
open scoped goldenRatio

namespace polyak.Threshold

open Spectral

/-- Article: the combined lag-one/minimizer integrand h_r. -/
def stripIntegrand (r u c : ℝ) : ℝ := (1-c^2-u^2)*(r-c)-2*u*(1-c^2)

/-- Article: averaging of h_r, expressed by finite moments. -/
def stripMean (ν : Spectrum) (r u : ℝ) : ℝ :=
  r*meanG ν u - avg ν (fun c => (1-(c:ℝ)^2-u^2)*(c:ℝ)) -
    2*u*avg ν (fun c => 1-(c:ℝ)^2)

/-- Article: exact integral representation of the combined inequality. -/
theorem stripMean_eq_integral (ν : Spectrum) (r u : ℝ) :
    stripMean ν r u = avg ν (fun c => stripIntegrand r u c) := by
  unfold stripMean
  rw [meanG_eq_integral]
  unfold stripIntegrand avg g
  have hg := integrable_continuous ν (show Continuous (fun c : Frequency =>
    1-(c:ℝ)^2-u^2) by fun_prop)
  have hc := integrable_continuous ν (show Continuous (fun c : Frequency =>
    (1-(c:ℝ)^2-u^2)*(c:ℝ)) by fun_prop)
  have hh := integrable_continuous ν (show Continuous (fun c : Frequency =>
    1-(c:ℝ)^2) by fun_prop)
  have heq : (fun c : Frequency => (1-(c:ℝ)^2-u^2)*(r-(c:ℝ))-2*u*(1-(c:ℝ)^2)) =
      (fun c : Frequency => r*(1-(c:ℝ)^2-u^2)-(1-(c:ℝ)^2-u^2)*(c:ℝ)-2*u*(1-(c:ℝ)^2)) := by
    funext c
    ring
  have hs := integral_sub ((hg.const_mul r).sub hc) (hh.const_mul (2*u))
  simp only [Pi.sub_apply] at hs
  have hs' := integral_sub (hg.const_mul r) hc
  rw [heq, hs, hs', integral_const_mul, integral_const_mul]

/-- Article: dependence on r is exactly the nonnegative minimizer slack. -/
theorem stripMean_add_r (ν : Spectrum) (r d u : ℝ) :
    stripMean ν (r+d) u = stripMean ν r u+d*meanG ν u := by
  unfold stripMean
  ring

/-- Article: lag-one Chebyshev normalization. -/
theorem chebT_one (c : ℝ) : chebT 1 c = c := by simp [chebT]

/-- Article: lag-one Chebyshev normalization. -/
theorem chebU_zero (c : ℝ) : chebU 0 c = 1 := by simp [chebU]

/-- Article: exact linear combination of lag one and the minimizer inequality. -/
theorem stripMean_cosh_add (ν : Spectrum) (u t s : ℝ) :
    stripMean ν (Real.cosh t+s) u = meanA ν u t 1-meanB ν u 1+s*meanG ν u := by
  unfold stripMean meanA meanB meanG
  simp only [Nat.cast_one, one_mul, Nat.sub_self, chebT_one, chebU_zero, mul_one]
  have heq : (fun c : Frequency => (1-(c:ℝ)^2-u^2)*(c:ℝ)) =
      (fun c : Frequency => (1-(c:ℝ)^2)*(c:ℝ)-u^2*(c:ℝ)) := by funext c; ring
  rw [heq]
  have h₁ := integrable_continuous ν (show Continuous (fun c : Frequency =>
    (1-(c:ℝ)^2)*(c:ℝ)) by fun_prop)
  have h₂ := integrable_continuous ν (show Continuous (fun c : Frequency => (c:ℝ)) by fun_prop)
  unfold avg
  rw [integral_sub h₁ (h₂.const_mul _), integral_const_mul]
  ring

/-- Article: exp(|t|)=cosh t+|sinh t|. -/
theorem exp_abs_eq_cosh_add_abs_sinh (t : ℝ) :
    Real.exp |t| = Real.cosh t+|Real.sinh t| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht),
      Real.cosh_eq, Real.sinh_eq]
    ring
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg ht', abs_of_neg (Real.sinh_neg_iff.mpr ht'),
      Real.cosh_eq, Real.sinh_eq]
    ring

/-- Article: the combined lag-one/minimizer inequality is nonnegative. -/
theorem feasibleU_stripMean_nonneg {ν : Spectrum} {u t C : ℝ}
    (h : FeasibleU u t ν C) : 0 ≤ stripMean ν (Real.exp |t|) u := by
  rw [exp_abs_eq_cosh_add_abs_sinh, stripMean_cosh_add]
  have hl := (h.2 1 (by omega)).1
  simp only [Nat.cast_one, one_mul] at hl
  have hmul : C*Real.sinh t ≤ |Real.sinh t| *meanG ν u := by
    calc
      _ ≤ |C*Real.sinh t| := le_abs_self _
      _ = |C| *|Real.sinh t| := abs_mul _ _
      _ ≤ meanG ν u*|Real.sinh t| := mul_le_mul_of_nonneg_right h.1 (abs_nonneg _)
      _ = _ := mul_comm _ _
  linarith

/-- Article: h_r decreases in nonnegative u. Proof: factor its exact difference. -/
theorem stripIntegrand_antitone {r u₀ u c : ℝ} (hr : 1 ≤ r)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) (hu₀ : 0 ≤ u₀) (hu : u₀ ≤ u) :
    stripIntegrand r u c ≤ stripIntegrand r u₀ c := by
  have hc2 : 0 ≤ 1-c^2 := by nlinarith [hc.1, hc.2]
  have hrc : 0 ≤ r-c := by linarith [hc.2]
  have hdiff : 0 ≤ (u-u₀)*((u+u₀)*(r-c)+2*(1-c^2)) :=
    mul_nonneg (sub_nonneg.mpr hu) (add_nonneg (mul_nonneg (by linarith) hrc) (by positivity))
  unfold stripIntegrand
  nlinarith [hdiff]

/-- Article: an explicit cubic bound at u=r/2. This is a stronger auxiliary certificate
than required by thresholdstrip, and is strict uniformly when r>1. -/
theorem stripIntegrand_half_le {r c : ℝ} (hr : 1 ≤ r)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    stripIntegrand r (r/2) c ≤ -(r-1)/4 := by
  have hfirst : (c-1)*(c+1/2)^2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hc.2]) (sq_nonneg _)
  have hbr : 1 ≤ r^2+r+1-c*(r+1) := by
    have h := mul_nonneg (show 0 ≤ r+1 by linarith) (show 0 ≤ 1-c by linarith [hc.2])
    nlinarith
  have hm := mul_nonneg (show 0 ≤ r-1 by linarith) (show 0 ≤ r^2+r+1-c*(r+1)-1 by linarith)
  have heq : stripIntegrand r (r/2) c =
      (c-1)*(c+1/2)^2-(r-1)*(r^2+r+1-c*(r+1))/4 := by unfold stripIntegrand; ring
  rw [heq]
  nlinarith

/-- Article: strict negativity after combining the constraints, uniformly over all frequencies. -/
theorem stripMean_neg_of_half_le {ν : Spectrum} {r u : ℝ} (hr : 1 < r) (hu : r/2 ≤ u) :
    stripMean ν r u < 0 := by
  have hbound : stripMean ν r u ≤ -(r-1)/4 := by
    rw [stripMean_eq_integral]
    have hi := integrable_continuous ν (show Continuous (fun c : Frequency =>
      stripIntegrand r u c) by unfold stripIntegrand; fun_prop)
    have hh := integral_mono hi (integrable_const (-(r-1)/4)) (fun c =>
      (stripIntegrand_antitone hr.le c.property (by linarith) hu).trans
        (stripIntegrand_half_le hr.le c.property))
    simpa [avg] using hh
  linarith

/-- Article: a nonnegative combined inequality and minimizer slack force u≤r/2.
Proof: a strict violation can be tested at a slightly larger r>1, using the nonnegative slack. -/
theorem le_half_of_stripMean_nonneg {ν : Spectrum} {r u : ℝ} (hr : 1 ≤ r)
    (hg : 0 ≤ meanG ν u) (hh : 0 ≤ stripMean ν r u) : u ≤ r/2 := by
  by_contra h
  have hu : r/2 < u := lt_of_not_ge h
  let d := (u-r/2)/2
  have hd : 0 < d := by dsimp [d]; linarith
  have hr' : 1 < r+d := by linarith
  have hu' : (r+d)/2 ≤ u := by dsimp [d]; linarith
  have hpos : 0 ≤ stripMean ν (r+d) u := by
    rw [stripMean_add_r]
    exact add_nonneg hh (mul_nonneg hd.le hg)
  exact (not_lt_of_ge hpos) (stripMean_neg_of_half_le hr' hu')

/-- Article: stronger intermediate bound on the nonnegative twist coordinate. -/
theorem feasibleU_u_le_exp_abs_half {ν : Spectrum} {u t C : ℝ}
    (h : FeasibleU u t ν C) : u ≤ Real.exp |t|/2 := by
  exact le_half_of_stripMean_nonneg (Real.one_le_exp (abs_nonneg _))
    ((abs_nonneg _).trans h.1) (feasibleU_stripMean_nonneg h)

/-- Article: absolute-twist version, valid also at u=0. -/
theorem feasibleU_abs_u_le_exp_abs_half {ν : Spectrum} {u t C : ℝ}
    (h : FeasibleU u t ν C) : |u| ≤ Real.exp |t|/2 := by
  rw [abs_le]
  exact ⟨by linarith [feasibleU_u_le_exp_abs_half ((feasibleU_neg_u_iff u t C ν).mpr h)],
    feasibleU_u_le_exp_abs_half h⟩

/-- Article: the exact golden-ratio hyperbolic identity underlying the printed strip. -/
theorem sinh_add_log_golden (a : ℝ) :
    Real.sinh (a+Real.log φ) = Real.exp a/2+Real.sinh a/φ := by
  have hp := Real.goldenRatio_pos
  have he : Real.exp (a+Real.log φ) = Real.exp a*φ := by rw [Real.exp_add, Real.exp_log hp]
  have hm : Real.exp (-(a+Real.log φ)) = Real.exp (-a)/φ := by
    rw [Real.exp_neg, he, mul_inv_rev, div_eq_mul_inv, Real.exp_neg]
    ring
  rw [Real.sinh_eq, he, hm, Real.sinh_eq]
  have hsq := congrArg (fun x : ℝ => Real.exp a*x) (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))
  field_simp
  nlinarith [hsq]

/-- Article: thresholdstrip, including all frequency endpoints, both signs and t=0. -/
theorem feasible_strip {ν : Spectrum} {v t C : ℝ} (h : Feasible v t ν C) :
    |v| ≤ |t|+Real.log φ := by
  have hu := feasibleU_abs_u_le_exp_abs_half h
  have habs : Real.sinh |v| = |Real.sinh v| := by
    by_cases hv : 0 ≤ v
    · rw [abs_of_nonneg hv, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hv)]
    · rw [abs_of_neg (lt_of_not_ge hv), Real.sinh_neg,
        abs_of_neg (Real.sinh_neg_iff.mpr (lt_of_not_ge hv))]
  apply Real.sinh_le_sinh.mp
  rw [habs, sinh_add_log_golden]
  have hh : 0 ≤ Real.sinh |t|/φ := div_nonneg (Real.sinh_nonneg_iff.mpr (abs_nonneg _))
    Real.goldenRatio_pos.le
  exact hu.trans (by linarith)

/-- Article: strict thresholdstrip away from the zero exponent. -/
theorem feasible_strip_strict {ν : Spectrum} {v t C : ℝ}
    (h : Feasible v t ν C) (ht : t ≠ 0) : |v| < |t|+Real.log φ := by
  have hu := feasibleU_abs_u_le_exp_abs_half h
  have habs : Real.sinh |v| = |Real.sinh v| := by
    by_cases hv : 0 ≤ v
    · rw [abs_of_nonneg hv, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hv)]
    · rw [abs_of_neg (lt_of_not_ge hv), Real.sinh_neg,
        abs_of_neg (Real.sinh_neg_iff.mpr (lt_of_not_ge hv))]
  apply Real.sinh_lt_sinh.mp
  rw [habs, sinh_add_log_golden]
  have hh : 0 < Real.sinh |t|/φ := div_pos (Real.sinh_pos_iff.mpr (abs_pos.mpr ht))
    Real.goldenRatio_pos
  linarith

end polyak.Threshold
