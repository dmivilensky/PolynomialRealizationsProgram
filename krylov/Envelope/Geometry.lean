import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, thm:E and cor:lm, envelope norm geometry.
Use: supply the exact orthogonal-envelope norm bound, both realization-comparison
bounds and an explicit norm-linearization remainder for the later actual
trajectory decomposition, including the regime near exhaustion.
Source: mathlib inner-product Pythagoras, reverse triangle and Cauchy--Schwarz
inequalities; elementary scalar square identities retain all true denominators.
-/

namespace krylov.Envelope
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthogonal response decomposition controls the true norm by its actual remainder.
Use: An orthogonal response decomposition controls the true norm by its actual remainder.
Article: main_krylov, thm:E and cor:lm, envelope norm geometry.
Proof: Use Pythagoras followed by the reverse triangle inequality. -/
theorem orthogonal_envelope_norm (u v r : E) (huv : inner ℝ u v=0) :
    |‖u+v+r‖-Real.sqrt (‖u‖^2+‖v‖^2)| ≤ ‖r‖ := by
  have he : ‖u+v‖=Real.sqrt (‖u‖^2+‖v‖^2) := by
    simpa only [pow_two] using norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr huv
  rw [← he]
  simpa only [add_sub_cancel_left] using abs_norm_sub_norm_le (u+v+r) (u+v)

/-- Two orthogonal realization components change the common-envelope norm by at most their larger norm.
Use: Two orthogonal realization components change the common-envelope norm by at most their larger norm.
Article: main_krylov, thm:E and cor:lm, envelope norm geometry.
Proof: Compare the genuine two squared Pythagorean norms; positivity gives both real difference bounds. -/
theorem orthogonal_norm_comparison (u v w : E) (huv : inner ℝ u v=0)
    (huw : inner ℝ u w=0) : |‖u+v‖-‖u+w‖| ≤ max ‖v‖ ‖w‖ := by
  -- Compare actual squared orthogonal norms before estimating either real norm difference.
  have hv := norm_add_sq_real u v
  have hw := norm_add_sq_real u w
  rw [huv] at hv
  rw [huw] at hw
  have hm₁ := le_max_left ‖v‖ ‖w‖
  have hm₂ := le_max_right ‖v‖ ‖w‖
  have hn₁ := norm_nonneg (u+v)
  have hn₂ := norm_nonneg (u+w)
  have hn₃ := norm_nonneg v
  have hn₄ := norm_nonneg w
  have hm : 0 ≤ max ‖v‖ ‖w‖ := hn₃.trans hm₁
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (‖u+v‖-‖u+w‖),sq_nonneg (max ‖v‖ ‖w‖-‖v‖),sq_nonneg (max ‖v‖ ‖w‖-‖w‖)]

/-- The same true realization comparison has the printed quadratic-over-common-norm bound whenever that norm is positive.
Use: The same true realization comparison has the printed quadratic-over-common-norm bound whenever that norm is positive.
Article: main_krylov, thm:E and cor:lm, envelope norm geometry.
Proof: Factor the two squared norms and keep both genuine denominator terms above the positive common norm. -/
theorem orthogonal_norm_comparison_quadratic (u v w : E) (hu : 0 < ‖u‖)
    (huv : inner ℝ u v=0) (huw : inner ℝ u w=0) :
    |‖u+v‖-‖u+w‖| ≤ (‖v‖^2+‖w‖^2)/(2*‖u‖) := by
  -- Both actual Pythagorean denominator terms dominate the same genuine positive common norm.
  have hv := norm_add_sq_real u v
  have hw := norm_add_sq_real u w
  rw [huv] at hv
  rw [huw] at hw
  have hx : ‖u‖ ≤ ‖u+v‖ := by nlinarith [norm_nonneg (u+v),sq_nonneg ‖v‖]
  have hy : ‖u‖ ≤ ‖u+w‖ := by nlinarith [norm_nonneg (u+w),sq_nonneg ‖w‖]
  rw [le_div_iff₀ (by positivity : 0 < 2*‖u‖)]
  by_cases he : ‖u+v‖ ≤ ‖u+w‖
  · rw [abs_of_nonpos (sub_nonpos.mpr he)]
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hx),mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hy),sq_nonneg ‖v‖]
  · have he' := le_of_lt (lt_of_not_ge he)
    rw [abs_of_nonneg (sub_nonneg.mpr he')]
    nlinarith [mul_nonneg (sub_nonneg.mpr he') (sub_nonneg.mpr hx),mul_nonneg (sub_nonneg.mpr he') (sub_nonneg.mpr hy),sq_nonneg ‖w‖]

/-- The real Hilbert norm has an explicit quadratic first-order remainder at every nonzero point.
Use: The real Hilbert norm has an explicit quadratic first-order remainder at every nonzero point.
Article: main_krylov, thm:E and cor:lm, envelope norm geometry.
Proof: Cauchy--Schwarz gives its supporting linear functional. The genuine norm-square identity bounds the remainder for small increments; the triangle inequality handles the complementary regime. -/
theorem norm_firstOrder_remainder (u h : E) (hu : 0 < ‖u‖) :
    |‖u+h‖-‖u‖-inner ℝ u h/‖u‖| ≤ 4*‖h‖^2/‖u‖ := by
  -- Retain the true nonzero reference norm throughout the scalar remainder estimate.
  let a := ‖u‖
  let b := inner ℝ u h/a
  let d := ‖h‖
  let x := ‖u+h‖
  have ha : 0 < a := hu
  have hd : 0 ≤ d := norm_nonneg _
  have hx : 0 ≤ x := norm_nonneg _
  have hba : b*a=inner ℝ u h := div_mul_cancel₀ _ ha.ne'
  have hinner := norm_inner_le_norm (𝕜 := ℝ) u h
  have hb : |b| ≤ d := by
    rw [abs_div,abs_of_pos ha,div_le_iff₀ ha]
    simpa only [Real.norm_eq_abs,mul_comm,a,d] using hinner
  have hb₁ := (abs_le.mp hb).1
  have hb₂ := (abs_le.mp hb).2
  have hxb : a+b ≤ x := by
    have hs := real_inner_le_norm u (u+h)
    rw [inner_add_right,real_inner_self_eq_norm_sq] at hs
    change a^2+inner ℝ u h ≤ a*x at hs
    nlinarith
  have hs : x^2=a^2+2*a*b+d^2 := by
    have hs := norm_add_sq_real u h
    change x^2=a^2+2*inner ℝ u h+d^2 at hs
    nlinarith
  change |x-a-b| ≤ 4*d^2/a
  rw [abs_of_nonneg (by linarith : 0 ≤ x-a-b),le_div_iff₀ ha]
  by_cases hsmall : d ≤ a/2
  · have hrem : 0 ≤ x-a-b := by linarith
    have hprod := mul_nonneg hrem (show 0 ≤ a+2*b by linarith)
    nlinarith [sq_nonneg b,sq_nonneg (x-a-b)]
  · have hlarge : a/2 ≤ d := (lt_of_not_ge hsmall).le
    have htriangle : x ≤ a+d := norm_add_le u h
    have hprod := mul_nonneg (show 0 ≤ 2*d-a by linarith) hd
    nlinarith

end
end krylov.Envelope
