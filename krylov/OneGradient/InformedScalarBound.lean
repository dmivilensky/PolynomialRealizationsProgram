import krylov.OneGradient.InformedConstant
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), full known-base scalar radius bound.
Use: the genuine correlated compression and hidden-pivot radius has the
exact original informed constant, including the zero-total-budget corner.
Source: exact positive scaling of the real square root and the genuine
attained compact variational maximum; no guessed maximizing parameter.
-/

namespace krylov.OneGradient
noncomputable section

/-- The full actual cross-action, hidden diagonal and known-base prior
radius is bounded by the exact original informed sharp constant.
Use: apply the genuine aggregate norm inequalities before constructing
true attaining physical operators and original source scenarios.
Article: main_krylov, thm:local(b), K_X(c).
Proof: if W is zero the actual cross radius is zero. Otherwise normalize
its true value by W and cancel exactly the positive-root scaling; the
result is the actual original objective at an admissible parameter. -/
theorem informed_scalar_bound {W w c r : ℝ} (hW : 0≤ W) (hc : 0≤ c)
    (hr : 0≤ r) (hrW : r≤ W) :
    r*Real.sqrt (W^2-r^2)+w*Real.sqrt (r^2+(c+Real.sqrt (W^2-r^2))^2)≤ informedConstant W w c := by
  by_cases hz : W=0
  · subst W
    have hre : r=0 := le_antisymm hrW hr
    rw [hre,informedConstant_zero w c hc]
    simp only [zero_pow (by decide : 2≠0),sub_self,Real.sqrt_zero,zero_mul,
      zero_add,add_zero,Real.sqrt_sq hc,le_refl]
  have hWp : 0< W := lt_of_le_of_ne hW (Ne.symm hz)
  let a := r/W
  have ha : a∈Set.Icc (0 : ℝ) 1 := ⟨div_nonneg hr hW,(div_le_one hWp).mpr hrW⟩
  have he : a*W=r := div_mul_cancel₀ r hz
  have hsq : a^2*W^2=r^2 := by rw [← mul_pow,he]
  have hroot : Real.sqrt (W^2-r^2)=W*Real.sqrt (1-a^2) := by
    have heq : W^2-r^2=W^2*(1-a^2) := by rw [← hsq];ring
    rw [heq,Real.sqrt_mul (sq_nonneg W),Real.sqrt_sq hW]
  have h := (informedConstant_variational W w c).2 a ha
  have heq : informedObjective W w c a=
      r*Real.sqrt (W^2-r^2)+w*Real.sqrt (r^2+(c+Real.sqrt (W^2-r^2))^2) := by
    rw [informedObjective,hroot,hsq]
    have he' := congrArg (fun x : ℝ => x*W*Real.sqrt (1-a^2)) he
    nlinarith
  exact heq ▸ h

end
end krylov.OneGradient
