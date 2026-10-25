import chebyshev1.SineJacobi.ProfileDerivatives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: chebyshev1, Theorem 5.2.
The descending Landen transformation, proved by an actual change of variables.
Use: `chebyshev1.SineJacobi.ellipticK_landen` feeds
`chebyshev2.SineContinuum.theta_elliptic_duplication` (The normalized elliptic integral is
invariant under theta duplication).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
Source: NIST Digital Library of Mathematical Functions, Chapter 19 — Landen quadratic
transformation. The needed form is proved here.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
Defines `landenMap` of type `ℝ` by `arcsin ((1+k)*sin theta/(1+k*sin theta^2))`.

Use: `chebyshev1.SineJacobi.ellipticK_landen` rewrites with this definition to establish
exact identity `ellipticK (2*sqrt k/(1+k)) = (1+k)*ellipticK k`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — Landen quadratic
transformation.
-/
private def landenMap (k theta : ℝ) : ℝ :=
  arcsin ((1+k)*sin theta/(1+k*sin theta^2))

/--
Defines `landenMap₁` of type `ℝ` by `(1+k)*(1-k*sin theta^2)/((1+k*sin theta^2)*sqrt (1-k^2*sin
theta^2))`.

Use:
`_private.chebyshev1.SineJacobi.EllipticLanden.0.chebyshev1.SineJacobi.landen_deriv`
uses this definition to establish the actual derivative at the stated point: `HasDerivAt
(landenMap k) (landenMap₁ k theta) theta`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — Landen quadratic
transformation.
-/
private def landenMap₁ (k theta : ℝ) : ℝ :=
  (1+k)*(1-k*sin theta^2)/((1+k*sin theta^2)*sqrt (1-k^2*sin theta^2))

/--
Exact identity `|(1+k)*s/(1+k*s^2)| < 1 ∧ sqrt (1-((1+k)*s/(1+k*s^2))^2) = c*sqrt
(1-k^2*s^2)/(1+k*s^2) ∧ sqrt (1-(2*sqrt k/(1+k))^2*((1+k)*s/(1+k*s^2))^2) =
(1-k*s^2)/(1+k*s^2)`.

Use:
`_private.chebyshev1.SineJacobi.EllipticLanden.0.chebyshev1.SineJacobi.landen_deriv`
uses this identity to establish the actual derivative at the stated point: `HasDerivAt
(landenMap k) (landenMap₁ k theta) theta`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — Landen quadratic
transformation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem landen_algebra {k s c : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hs : 0 ≤ s) (hc : 0 < c) (hsc : s^2+c^2 = 1) :
    |(1+k)*s/(1+k*s^2)| < 1 ∧
    sqrt (1-((1+k)*s/(1+k*s^2))^2) = c*sqrt (1-k^2*s^2)/(1+k*s^2) ∧
    sqrt (1-(2*sqrt k/(1+k))^2*((1+k)*s/(1+k*s^2))^2) =
      (1-k*s^2)/(1+k*s^2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs2 : s^2 < 1 := by nlinarith [sq_pos_of_pos hc]
  have hs1 : s < 1 := by nlinarith
  have hd : 0 < 1+k*s^2 := by positivity
  have hkp : 0 < 1+k := by positivity
  have hk2 : k^2 < 1 := by nlinarith
  have hr : 0 < 1-k^2*s^2 := by nlinarith [sq_nonneg k, mul_nonneg hk (sq_nonneg s)]
  have ha : (1+k)*s < 1+k*s^2 := by
    have ht : 0 < (1-s)*(1-k*s) := by
      apply mul_pos (by linarith)
      have : k*s < 1 := (mul_le_of_le_one_right hk hs1.le).trans_lt hk1
      linarith
    nlinarith
  have hab : |(1+k)*s/(1+k*s^2)| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hd]
    exact ha
  have hsq : 1-((1+k)*s/(1+k*s^2))^2 =
      (c*sqrt (1-k^2*s^2)/(1+k*s^2))^2 := by
    simp only [div_pow, mul_pow, sq_sqrt hr.le]
    field_simp
    nlinarith [hsc]
  have hsqr : sqrt (1-((1+k)*s/(1+k*s^2))^2) =
      c*sqrt (1-k^2*s^2)/(1+k*s^2) := by
    rw [hsq, sqrt_sq (by positivity)]
  have he : 1-(2*sqrt k/(1+k))^2*((1+k)*s/(1+k*s^2))^2 =
      ((1-k*s^2)/(1+k*s^2))^2 := by
    rw [div_pow, mul_pow, sq_sqrt hk]
    field_simp
    ring
  have hn : 0 ≤ (1-k*s^2)/(1+k*s^2) := by
    apply div_nonneg _ hd.le
    have ht : k*s^2 < 1 := (mul_le_of_le_one_right hk hs2.le).trans_lt hk1
    linarith
  exact ⟨hab, hsqr, by rw [he, sqrt_sq hn]⟩

/--
The actual derivative at the stated point: `HasDerivAt (landenMap k) (landenMap₁ k theta)
theta`.

Use: `chebyshev1.SineJacobi.ellipticK_landen` uses this derivative formula to establish
exact identity `ellipticK (2*sqrt k/(1+k)) = (1+k)*ellipticK k`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — Landen quadratic
transformation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem landen_deriv {k theta : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (ht : theta ∈ Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt (landenMap k) (landenMap₁ k theta) theta := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs : 0 ≤ sin theta := (sin_pos_of_mem_Ioo ⟨ht.1, by linarith [ht.2, pi_pos]⟩).le
  have hc : 0 < cos theta := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, ht.1], ht.2⟩
  have ha := landen_algebra hk hk1 hs hc (sin_sq_add_cos_sq theta)
  have hd : 0 < 1+k*sin theta^2 := by positivity
  have hq := ((hasDerivAt_sin theta).const_mul (1+k)).div
    (((hasDerivAt_sin theta).pow 2).const_mul k |>.const_add 1) hd.ne'
  have hh := (hasDerivAt_arcsin (ne_of_gt (abs_lt.mp ha.1).1)
    (ne_of_lt (abs_lt.mp ha.1).2)).comp theta hq
  convert hh using 1
  · rfl
  · unfold landenMap₁
    simp only [Pi.pow_apply, pow_one, Nat.reduceSub, Nat.cast_ofNat]
    rw [ha.2.1]
    have hr : sqrt (1-k^2*sin theta^2) ≠ 0 := by
      apply (sqrt_pos.mpr _).ne'
      exact elliptic_den_pos k theta (by rw [abs_of_nonneg hk]; exact hk1)
    generalize sin theta = s at hd ⊢
    generalize cos theta = c at hc ⊢
    generalize sqrt (1-k^2*s^2) = r at hr ⊢
    field_simp [hd.ne', hc.ne', hr]
    ring

/--
The descending Landen transformation, proved by an actual change of variables. It provides a
rapidly convergent route to rigorous elliptic-integral certificates.

Exact identity `ellipticK (2*sqrt k/(1+k)) = (1+k)*ellipticK k`.

Use: `chebyshev1.SineJacobi.ellipticA_descent` uses this identity to establish exact
identity `ellipticA x = (1+descendingModulus x)*ellipticA (descendingModulus x^2)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — Landen quadratic
transformation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ellipticK_landen {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) :
    ellipticK (2*sqrt k/(1+k)) = (1+k)*ellipticK k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd (theta : ℝ) : 0 < 1+k*sin theta^2 := by positivity
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : Continuous (landenMap k) := by
    unfold landenMap
    exact continuous_arcsin.comp
      ((continuous_const.mul continuous_sin).div (by fun_prop) (fun theta => (hd theta).ne'))
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0:ℝ)) (b := Real.pi/2) (f := landenMap k) (f' := landenMap₁ k)
    (g := fun theta => 1/sqrt (1-(2*sqrt k/(1+k))^2*sin theta^2))
    hcont.continuousOn
    (fun theta ht => landen_deriv hk hk1 (by
      rw [min_eq_left (half_pos pi_pos).le, max_eq_right (half_pos pi_pos).le] at ht
      exact ht))
    (fun theta ht => by
      unfold landenMap₁
      have hsin : sin theta^2 ≤ 1 := sin_sq_le_one theta
      apply div_nonneg (mul_nonneg (by positivity) _) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hsin hk])
  have h0 : landenMap k 0 = 0 := by simp [landenMap]
  have h1 : landenMap k (Real.pi/2) = Real.pi/2 := by
    simp [landenMap, div_self (show 1+k ≠ 0 by positivity)]
  rw [h0, h1] at hs
  unfold ellipticK
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro theta ht
  rw [uIoo_of_le (half_pos pi_pos).le] at ht
  have hsin : 0 ≤ sin theta := (sin_pos_of_mem_Ioo ⟨ht.1, by linarith [ht.2, pi_pos]⟩).le
  have hcos : 0 < cos theta := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, ht.1], ht.2⟩
  have ha := landen_algebra hk hk1 hsin hcos (sin_sq_add_cos_sq theta)
  have harg : sin (landenMap k theta) = (1+k)*sin theta/(1+k*sin theta^2) := by
    unfold landenMap
    exact sin_arcsin (abs_lt.mp ha.1).1.le (abs_lt.mp ha.1).2.le
  simp only [Function.comp_def]
  rw [harg, ha.2.2]
  unfold landenMap₁
  have hd' := hd theta
  have hn : 0 < 1-k*sin theta^2 := by
    nlinarith [mul_le_mul_of_nonneg_left (sin_sq_le_one theta) hk]
  have hr : sqrt (1-k^2*sin theta^2) ≠ 0 :=
    (sqrt_pos.mpr (elliptic_den_pos k theta (by rw [abs_of_nonneg hk]; exact hk1))).ne'
  generalize sin theta = s at hd' hn ⊢
  generalize sqrt (1-k^2*s^2) = r at hr ⊢
  field_simp [hd'.ne', hn.ne', hr]

end
end chebyshev1.SineJacobi
