import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
Article: 2606.16671v2, Theorem E.3.
The error of replacing a midpoint by the average of the two endpoints.
Use: `«2606.16671v2».Analysis.midpoint_error_bound` feeds
`«2606.16671v2».SineJacobi.logRatio_error_bound` (Uniform quantitative correction of the finite sine
ratio by the half-binomial ratio).
Proof chain: `«2606.16671v2».SineJacobi.ratio_scaled_limit` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.Calculus.MeanValue, Mathlib.Analysis.Calculus.ContDiff.Deriv —
Taylor remainder and midpoint interpolation error. The needed form is proved here.
-/
namespace «2606.16671v2».Analysis
noncomputable section
open Set Real

/--
The stated quantitative bound `|f x-f a-f' a*(x-a)| ≤ M*(x-a)^2`.

Use: `«2606.16671v2».Analysis.midpoint_error_bound` uses this bound to establish the stated
quantitative bound `|f ((a+b)/2)-(f a+f b)/2| ≤ M*(b-a)^2`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.Calculus.MeanValue, Mathlib.Analysis.Calculus.ContDiff.Deriv
— Taylor remainder and midpoint interpolation error.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem first_order_error_bound {f f' f'' : ℝ → ℝ} {a b x M : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hbnd : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |f x-f a-f' a*(x-a)| ≤ M*(x-a)^2 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hlip : ∀ t ∈ Icc a x, |f' t-f' a| ≤ M*(x-a) := by
    intro t ht
    have hti : t ∈ Icc a b := ⟨ht.1, ht.2.trans hx.2⟩
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hf' u hu).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hbnd u hu)
      ⟨le_rfl, hab⟩ hti
    simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hM)
  let F : ℝ → ℝ := fun t => f t-f a-f' a*(t-a)
  have hF : ∀ t ∈ Icc a x, HasDerivAt F (f' t-f' a) t := by
    intro t ht
    convert ((hf t ⟨ht.1, ht.2.trans hx.2⟩).sub_const (f a)).sub
      (((hasDerivAt_id t).sub_const a).const_mul (f' a)) using 1
    · funext u; rfl
    · simp
  have h := (convex_Icc a x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hF t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hlip t ht)
    ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩
  simpa only [F, sub_self, mul_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hx.1), ← pow_two, mul_assoc] using h

/--
The error of replacing a midpoint by the average of the two endpoints.

The stated quantitative bound `|f ((a+b)/2)-(f a+f b)/2| ≤ M*(b-a)^2`.

Use: `«2606.16671v2».SineJacobi.logRatio_error_bound` uses this bound to establish the stated
quantitative bound `|logRatio N k+logSinc ((k:ℝ)/N)/2| ≤ M*(k:ℝ)/(N:ℝ)^2`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.Calculus.MeanValue, Mathlib.Analysis.Calculus.ContDiff.Deriv
— Taylor remainder and midpoint interpolation error.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.first_order_error_bound` with the
arguments shown in the proof.
-/
theorem midpoint_error_bound {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hbnd : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |f ((a+b)/2)-(f a+f b)/2| ≤ M*(b-a)^2 := by
  -- Use the identities/estimates `«2606.16671v2».Analysis.first_order_error_bound` with the
  -- arguments shown in the proof.
  have hm := first_order_error_bound hab
    (show (a+b)/2 ∈ Icc a b by constructor <;> linarith) hM hf hf' hbnd
  have hr := first_order_error_bound hab ⟨hab, le_rfl⟩ hM hf hf' hbnd
  have htri := norm_sub_le (f ((a+b)/2)-f a-f' a*((a+b)/2-a))
    ((f b-f a-f' a*(b-a))/2)
  simp only [Real.norm_eq_abs] at htri
  have he : f ((a+b)/2)-(f a+f b)/2 =
      (f ((a+b)/2)-f a-f' a*((a+b)/2-a))-(f b-f a-f' a*(b-a))/2 := by ring
  rw [he]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)] at htri
  have hs : ((a+b)/2-a)^2 = (b-a)^2/4 := by ring
  rw [hs] at hm
  nlinarith [sq_nonneg (b-a)]

end
end «2606.16671v2».Analysis
