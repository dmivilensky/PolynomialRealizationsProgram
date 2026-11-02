import jacobi.RootMass.Replacement
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
An actual quadratic remainder bounded by the square of a vanishing
first-order primitive has zero right derivative. The same right-derivative
calculus turns the genuine minimizing property into the needed nonnegative
needle derivative, without a hidden two-sided admissibility assumption.
Source: little-o calculus and the one-sided derivative definition.
Use: controls the true signed spectral second-moment remainder in the needle minimum principle.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set Filter Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A genuine quadratic primitive bound forces zero derivative of the actual remainder on the admissible right half-line.
Use: controls the true signed spectral second-moment remainder in the needle minimum principle.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the differentiable vanishing primitive is O(epsilon), so its square
is O(epsilon²)=o(epsilon). The actual remainder inherits this little-o bound. -/
theorem quadratic_remainder {R L : ℝ → ℝ} {d : ℝ} (hR0 : R 0=0) (hL0 : L 0=0)
    (hL : HasDerivAt L d 0) (hbound : ∀ eps : ℝ,0≤eps → |R eps|≤(L eps)^2) :
    HasDerivWithinAt R 0 (Ici (0:ℝ)) 0 := by
  -- Only the nonnegative-width side is used; negative-width needles need not be admissible variations.
  have hRL : R =O[𝓝[Ici (0:ℝ)] 0] (fun eps => (L eps)^2) := by
    apply IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin] with eps heps
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (L eps)),one_mul] using hbound eps heps
  have hLO : L =O[𝓝 (0:ℝ)] (fun eps => eps) := by
    simpa only [hL0,sub_zero] using hL.isBigO_sub
  have hsmall := (hRL.trans ((hLO.pow 2).mono nhdsWithin_le_nhds)).trans_isLittleO
    ((isLittleO_pow_id (by decide : 1<2) (𝕜 := ℝ)).mono nhdsWithin_le_nhds)
  apply HasDerivWithinAt.of_isLittleO
  simpa only [hR0,sub_zero,smul_zero] using hsmall

/-- The right derivative at an actual constrained local minimum is nonnegative.
Use: extracts the scalar needle inequality from the original variational minimizing property.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the derivative is the limit of right secant slopes. Every sufficiently
small admissible positive-width secant is nonnegative, so its limit is nonnegative. -/
theorem right_derivative_nonneg {F : ℝ → ℝ} {d : ℝ}
    (hF : HasDerivWithinAt F d (Ici (0:ℝ)) 0)
    (hmin : ∀ᶠ eps in 𝓝[Ici (0:ℝ)] 0,F 0≤F eps) : 0≤d := by
  have hd := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ)∉Ioi 0 by simp)).mp
    (hF.mono Ioi_subset_Ici_self)
  apply ge_of_tendsto hd
  filter_upwards [hmin.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self),self_mem_nhdsWithin] with eps he heps
  rw [slope_def_field,sub_zero]
  exact div_nonneg (sub_nonneg.mpr he) (le_of_lt heps)

end
end jacobi.RootMass
