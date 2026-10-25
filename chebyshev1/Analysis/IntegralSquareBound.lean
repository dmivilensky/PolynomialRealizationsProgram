import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
Article: chebyshev1, Theorem 5.2.
Integral Square Bound.
Use: `chebyshev1.Analysis.integral_square_bound` feeds
`chebyshev1.SineJacobi.ellipticK_square_bound` (Cauchy--Schwarz and the elementary rational
integral give a uniform bound for K²).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi` — chebyshev1, Theorem 5.2;
Exact sine gain, resolvent expression, asymptotics and energy value.
Source: mathlib, Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic, Mathlib.Tactic —
Cauchy–Schwarz for a finite interval integral. The needed form is proved here.
-/
namespace chebyshev1.Analysis
noncomputable section
open MeasureTheory

/--
The stated quantitative bound `(∫ x in a..b, f x)^2 ≤ (b-a)*(∫ x in a..b, f x^2)`.

Use: `chebyshev1.SineJacobi.ellipticK_square_bound` uses this bound to establish the stated
quantitative bound `ellipticK k^2 ≤ Real.pi^2/(4*sqrt (1-k^2))`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_le_four_div_pi`.

Source: mathlib, Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic, Mathlib.Tactic —
Cauchy–Schwarz for a finite interval integral.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem integral_square_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h1 : IntervalIntegrable f volume a b)
    (h2 : IntervalIntegrable (fun x => f x^2) volume a b) :
    (∫ x in a..b, f x)^2 ≤ (b-a)*(∫ x in a..b, f x^2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let m := (∫ x in a..b, f x)/(b-a)
  have he : (∫ x in a..b, (f x-m)^2) =
      (∫ x in a..b, f x^2)-(∫ x in a..b, f x)^2/(b-a) := by
    have hf : (fun x => (f x-m)^2) = fun x => f x^2-2*m*f x+m^2 := by funext x; ring
    rw [hf, intervalIntegral.integral_add (h2.sub (h1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub h2 (h1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    dsimp [m]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun x => sq_nonneg (f x-m))
  rw [he] at hn
  have hh := (div_le_iff₀ (sub_pos.mpr hab)).mp (sub_nonneg.mp hn)
  simpa only [mul_comm] using hh

end
end chebyshev1.Analysis
