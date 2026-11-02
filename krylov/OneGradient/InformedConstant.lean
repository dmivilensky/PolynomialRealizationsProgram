import krylov.Correction.SharpConstant
import Mathlib.Topology.Order.Compact
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), genuine known-base sharp scalar functional.
Use: retain the full unmeasured last-pivot tradeoff, including zero budgets,
and provide a genuine attained maximum for later physical sharpness.
Source: continuity on the real compact unit interval and exact real algebra.
-/

namespace krylov.OneGradient
noncomputable section
open Set

/-- The original known-base second-order scalar objective, with its full
unmeasured pivot and output-defect contributions.
Use: define the exact original informed sharp constant, including zero budgets.
Article: main_krylov, thm:local(b), K_X(c). -/
def informedObjective (W w c a : ℝ) : ℝ :=
  a*W^2*Real.sqrt (1-a^2)+w*Real.sqrt (a^2*W^2+(c+W*Real.sqrt (1-a^2))^2)

/-- The original known-base sharp scalar constant as the actual compact
maximum value, rather than a supplied upper bound or an optimizer field.
Use: exact variational bounds and actual attaining primitive coefficients.
Article: main_krylov, thm:local(b), K_X(c). -/
def informedConstant (W w c : ℝ) : ℝ := sSup (informedObjective W w c '' Icc 0 1)

/-- The actual known-base scalar objective is continuous, including all
unit-interval corners and every zero budget.
Use: derive the genuine attained sharp maximum without an interior-domain
or differentiability assumption at a collapsed square root.
Article: main_krylov, thm:local(b).
Proof: all primitive real operations and the genuine nonnegative square
root are continuous globally. -/
theorem informedObjective_continuous (W w c : ℝ) : Continuous (informedObjective W w c) := by
  unfold informedObjective
  fun_prop

/-- The full original known-base sharp scalar functional has a genuine
maximizer and equals its actual value there; every admissible coefficient
is bounded by this exact attained maximum, including zero budgets.
Use: both the true operator upper estimate and primitive physical lower
witness use the same actual maximizer.
Article: main_krylov, thm:local(b).
Proof: the actual objective has a compact nonempty image, so the real
supremum belongs to that image and bounds every one of its values. -/
theorem informedConstant_variational (W w c : ℝ) :
    (∃ a∈Icc (0 : ℝ) 1,informedObjective W w c a=informedConstant W w c) ∧
      ∀ a∈Icc (0 : ℝ) 1,informedObjective W w c a≤ informedConstant W w c := by
  have hK := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (informedObjective_continuous W w c)
  have hn : (informedObjective W w c '' Icc (0 : ℝ) 1).Nonempty :=
    (nonempty_Icc.mpr zero_le_one).image _
  exact ⟨hK.sSup_mem hn,fun a ha => le_csSup hK.bddAbove ⟨a,ha,rfl⟩⟩

/-- With no observed curvature increments, the exact known-base scalar
constant is precisely the hidden-base times output-defect product.
Use: the original zero-total-budget corner is included in the full formula.
Article: main_krylov, thm:local(b), K_X(c)=cw' when W=0.
Proof: every actual scalar value is the same product; evaluate the genuine
maximum at its attained parameter. -/
theorem informedConstant_zero (w c : ℝ) (hc : 0≤ c) : informedConstant 0 w c=w*c := by
  obtain ⟨a,_,ha⟩ := (informedConstant_variational 0 w c).1
  rw [← ha,informedObjective]
  simp only [zero_pow (by decide : 2≠0),mul_zero,zero_mul,add_zero,zero_add,Real.sqrt_sq hc]

end
end krylov.OneGradient
