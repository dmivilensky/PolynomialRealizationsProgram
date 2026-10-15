import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: 2606.16671v2, Theorem 5.2.
A deliberately simple fourth-order error bound, derived from mathlib's Taylor theorem.
Use: `«2606.16671v2».Analysis.simpson_error` feeds
`«2606.16671v2».SineJacobi.sineEnergy_quadrature_error` (sine Energy quadrature error).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
Source: mathlib, Mathlib.Analysis.Calculus.Taylor,
Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus — Simpson quadrature with a
fourth-derivative remainder. The needed form is proved here.
-/
namespace «2606.16671v2».Analysis
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
One Simpson panel, with midpoint `(a+b)/2`.

Use: `_private.«2606.16671v2».Analysis.Simpson.0.«2606.16671v2».Analysis.simpson_cubic` uses
this definition to establish the identity `(∫ x in a..b, A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) =
simpson (fun x => A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) a b`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.Taylor,
Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus — Simpson quadrature with a
fourth-derivative remainder.
-/
def simpson (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b-a)/6*(f a+4*f ((a+b)/2)+f b)

/--
Exact identity `(∫ x in a..b, A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) = simpson (fun x =>
A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) a b`.

Use: `_private.«2606.16671v2».Analysis.Simpson.0.«2606.16671v2».Analysis.simpson_taylor` uses
this identity to establish the identity `(∫ x in a..b, taylorWithinEval f 3 (Icc a b) a x) =
simpson (taylorWithinEval f 3 (Icc a b) a) a b`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.Taylor,
Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus — Simpson quadrature with a
fourth-derivative remainder.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
private theorem simpson_cubic (a b A B C D : ℝ) :
    (∫ x in a..b, A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) =
      simpson (fun x => A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) a b := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let F : ℝ → ℝ := fun x => A*(x-a)+(B/2)*(x-a)^2+(C/3)*(x-a)^3+(D/4)*(x-a)^4
  have hd (x : ℝ) : HasDerivAt F (A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) x := by
    have hx := (hasDerivAt_id x).sub_const a
    convert (((hx.const_mul A).add ((hx.pow 2).const_mul (B/2))).add
      ((hx.pow 3).const_mul (C/3))).add ((hx.pow 4).const_mul (D/4)) using 1
    · funext y; rfl
    · dsimp; ring
  have hi : IntervalIntegrable (fun x => A+B*(x-a)+C*(x-a)^2+D*(x-a)^3) volume a b :=
    (by fun_prop : Continuous _).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  dsimp [F, simpson]
  ring

/--
Exact identity `(∫ x in a..b, taylorWithinEval f 3 (Icc a b) a x) = simpson (taylorWithinEval f
3 (Icc a b) a) a b`.

Use: `«2606.16671v2».Analysis.simpson_error` rewrites with this identity to establish the
stated quantitative bound `|(∫ x in a..b, f x)-simpson f a b| ≤ M*(b-a)^5/3`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.Taylor,
Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus — Simpson quadrature with a
fourth-derivative remainder.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
private theorem simpson_taylor (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, taylorWithinEval f 3 (Icc a b) a x) =
      simpson (taylorWithinEval f 3 (Icc a b) a) a b := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : taylorWithinEval f 3 (Icc a b) a = fun x =>
      f a + iteratedDerivWithin 1 f (Icc a b) a*(x-a)+
      (iteratedDerivWithin 2 f (Icc a b) a/2)*(x-a)^2+
      (iteratedDerivWithin 3 f (Icc a b) a/6)*(x-a)^3 := by
    funext x
    simp only [show 3 = 2+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval,
      Nat.factorial, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, smul_eq_mul]
    ring
  rw [he]
  exact simpson_cubic _ _ _ _ _ _

/--
A deliberately simple fourth-order error bound, derived from mathlib's Taylor theorem.

The stated quantitative bound `|(∫ x in a..b, f x)-simpson f a b| ≤ M*(b-a)^5/3`.

Use: `«2606.16671v2».SineJacobi.sineEnergy_quadrature_error` uses this bound to establish the
stated quantitative bound `|sineEnergy-energyQuadrature N| ≤ 1300000/(3*(N:ℝ)^4)+12/(N:ℝ)^6`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.Taylor,
Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus — Simpson quadrature with a
fourth-derivative remainder.

Proof: Use the identities/estimates
`_private.«2606.16671v2».Analysis.Simpson.0.«2606.16671v2».Analysis.simpson_taylor` with the
arguments shown in the proof.
-/
theorem simpson_error {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b) (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hder : ∀ x ∈ Icc a b, |iteratedDerivWithin 4 f (Icc a b) x| ≤ M) :
    |(∫ x in a..b, f x)-simpson f a b| ≤ M*(b-a)^5/3 := by
  -- Use the identities/estimates
  -- `_private.«2606.16671v2».Analysis.Simpson.0.«2606.16671v2».Analysis.simpson_taylor` with
  -- the arguments shown in the proof.
  let P := taylorWithinEval f 3 (Icc a b) a
  let R := fun x => f x-P x
  -- Establish continuity hp before using the function at limits or in calculus arguments.
  have hp : Continuous P := by
    change Continuous (fun x => taylorWithinEval f 3 (Icc a b) a x)
    simp only [show 3 = 2+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval, smul_eq_mul]
    fun_prop
  have hbnd (x : ℝ) (hx : x ∈ Icc a b) : |R x| ≤ M*(b-a)^4/6 := by
    have hh := taylor_mean_remainder_bound (n := 3) hab.le hf hx (fun y hy => by
      simpa only [Real.norm_eq_abs] using hder y hy)
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one] at hh
    exact hh.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) 4) hM)
      (by norm_num))
  have hI : |∫ x in a..b, R x| ≤ M*(b-a)^5/6 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := M*(b-a)^4/6) (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hbnd x ⟨(uIoc_of_le hab.le ▸ hx).1.le, (uIoc_of_le hab.le ▸ hx).2⟩)
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at hh
    convert hh using 1; ring
  have hS : |simpson R a b| ≤ M*(b-a)^5/6 := by
    rw [simpson, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (b-a)/6)]
    have ha := hbnd a (left_mem_Icc.mpr hab.le)
    have hb := hbnd b (right_mem_Icc.mpr hab.le)
    have hc := hbnd ((a+b)/2) ⟨by linarith, by linarith⟩
    have hsum : |R a+4*R ((a+b)/2)+R b| ≤ |R a|+4*|R ((a+b)/2)|+|R b| := by
      have hh := (abs_add_le (R a+4*R ((a+b)/2)) (R b)).trans
        (add_le_add (abs_add_le (R a) (4*R ((a+b)/2))) le_rfl)
      simpa only [abs_mul, show |(4:ℝ)| = 4 by norm_num] using hh
    have hh := mul_le_mul_of_nonneg_left (hsum.trans (show |R a|+4*|R ((a+b)/2)|+|R b| ≤ M*(b-a)^4 by linarith))
      (show 0 ≤ (b-a)/6 by positivity)
    convert hh using 1; ring
  have he : (∫ x in a..b, f x)-simpson f a b = (∫ x in a..b, R x)-simpson R a b := by
    rw [intervalIntegral.integral_sub
      (hf.continuousOn.intervalIntegrable_of_Icc hab.le)
      (hp.intervalIntegrable a b)]
    rw [simpson_taylor]
    dsimp [P, R, simpson]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

end
end «2606.16671v2».Analysis
