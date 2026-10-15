import «2610.05164v2».Packing.Blocks
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: 2610.05164v2, Theorem 2.3.
Exact first-moment cost of moving a uniform interval to a point inside it.
Use: `«2610.05164v2».Packing.interval_transport_cost_bound` feeds
`«2610.05164v2».Packing.Blocks.coupling_cost` (The actual transport cost, bounded uniformly over the
location inside each cell).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Packing
noncomputable section
open MeasureTheory Real Set

/--
Exact first-moment cost of moving a uniform interval to a point inside it.

Exact identity `(∫ x in Ioc l r, |x-y|) = ((y-l)^2+(r-y)^2)/2`.

Use: `«2610.05164v2».Packing.interval_transport_cost_bound` rewrites with this identity to
establish the stated quantitative bound `(∫ x in Ioc l r, |x-y|) ≤ (r-l)^2/2`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem interval_transport_cost {l r y : ℝ} (hy : y ∈ Icc l r) :
    (∫ x in Ioc l r, |x-y|) = ((y-l)^2+(r-y)^2)/2 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hl := integral_pow_abs_sub_uIoc (a := y) (b := l) (n := 1)
  have hr := integral_pow_abs_sub_uIoc (a := y) (b := r) (n := 1)
  rw [uIoc_of_ge hy.1] at hl
  rw [uIoc_of_le hy.2] at hr
  simp only [pow_one,Nat.reduceAdd] at hl hr
  rw [abs_sub_comm l y,abs_of_nonneg (sub_nonneg.mpr hy.1)] at hl
  rw [abs_of_nonneg (sub_nonneg.mpr hy.2)] at hr
  have h₁ : IntervalIntegrable (fun x => |x-y|) volume l y :=
    (continuous_id.sub continuous_const).abs.intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun x => |x-y|) volume y r :=
    (continuous_id.sub continuous_const).abs.intervalIntegrable _ _
  have hadd := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  rw [intervalIntegral.integral_of_le hy.1,intervalIntegral.integral_of_le hy.2,
    intervalIntegral.integral_of_le (hy.1.trans hy.2),hl,hr] at hadd
  linarith

/--
The stated quantitative bound `(∫ x in Ioc l r, |x-y|) ≤ (r-l)^2/2`.

Use: `«2610.05164v2».Packing.Blocks.coupling_cost` uses this bound to establish the stated
quantitative bound `(∫ z, |z.1-z.2| ∂B.coupling y) ≤ ∑ i, B.height i^2 * (B.right i-B.left
i)^2/2`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Packing.interval_transport_cost` with the
arguments shown in the proof.
-/
theorem interval_transport_cost_bound {l r y : ℝ} (hy : y ∈ Icc l r) :
    (∫ x in Ioc l r, |x-y|) ≤ (r-l)^2/2 := by
  rw [interval_transport_cost hy]
  nlinarith [mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)]

end
end «2610.05164v2».Packing
