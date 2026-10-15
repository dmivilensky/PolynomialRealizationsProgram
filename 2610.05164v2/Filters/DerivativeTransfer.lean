import «2610.05164v2».Filters.Cumulative
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: 2610.05164v2, Proposition 3.
A nuclear first-order approximation only needs positive increments.
Use: `«2610.05164v2».Filters.hasDerivAt_of_right_increment_bound` feeds
`«2610.05164v2».Filters.leftLogDeterminant_hasDerivAt` (left Log Determinant has Deriv At).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
A nuclear first-order approximation only needs positive increments. Absolute continuity
supplies differentiability of the scalar function AE.

The actual derivative at the stated point: `HasDerivAt f c x`.

Use: `«2610.05164v2».Filters.leftLogDeterminant_hasDerivAt` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (leftLogDeterminant hm hn s)
(s*m x/(2+nonlinear s m x)) x`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem hasDerivAt_of_right_increment_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f F : ℝ → ℝ} {g : ℝ → E} {dg : E} {x c K : ℝ}
    (hf : DifferentiableAt ℝ f x) (hF : HasDerivAt F c x) (hg : HasDerivAt g dg x)
    (hbound : ∀ y, x < y → ‖(f y-f x)-(F y-F x)‖ ≤ K*‖g y-g x-(y-x) • dg‖) :
    HasDerivAt f c x := by
  -- Record the convergence hs with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hs (p : ℝ → ℝ) (d : ℝ) (hp : HasDerivAt p d x) :
      Tendsto (slope p x) (𝓝[>] x) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi x) (by simp)).mp hp.hasDerivWithinAt
  -- Record the convergence hgs with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hgs : Tendsto (slope g x) (𝓝[>] x) (𝓝 dg) :=
    (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi x) (by simp)).mp hg.hasDerivWithinAt
  have hleft := ((hs f _ hf.hasDerivAt).sub (hs F c hF)).norm
  have hright := (hgs.sub_const dg).norm.const_mul K
  simp only [sub_self,norm_zero,mul_zero] at hright
  have hle : ‖deriv f x-c‖ ≤ 0 := by
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hpos : 0 < y-x := sub_pos.mpr hy
    have he : slope f x y-slope F x y = (y-x)⁻¹ • ((f y-f x)-(F y-F x)) := by
      simp only [slope_def_module,smul_sub]
    have hr : g y-g x-(y-x) • dg = (y-x) • (slope g x y-dg) := by
      rw [slope_def_module,smul_sub,smul_smul,mul_inv_cancel₀ hpos.ne',one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    calc
      _ ≤ (y-x)⁻¹*(K*‖g y-g x-(y-x) • dg‖) :=
        mul_le_mul_of_nonneg_left (hbound y hy) (inv_nonneg.mpr hpos.le)
      _ = K*‖slope g x y-dg‖ := by
        rw [hr,norm_smul,Real.norm_eq_abs,abs_of_pos hpos]
        field_simp
  have he : deriv f x=c := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))
  exact he ▸ hf.hasDerivAt

end
end «2610.05164v2».Filters
