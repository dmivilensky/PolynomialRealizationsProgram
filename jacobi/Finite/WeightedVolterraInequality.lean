import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The genuine complex weighted Volterra equation implies its original
positive scalar linear-kernel inequality. This shared bridge is used
by both the exponential and factorial/cosh comparisons.
Use: weighted_volterra_cosh and weighted_volterra_bound compare actual support-wave norms using the proved explicit positive scalar majorants.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- The actual complex Volterra equation implies the genuine positive weighted scalar inequality with the same original linear kernel.
Use: weighted_volterra_cosh and weighted_volterra_bound compare actual support-wave norms using the proved explicit positive scalar majorants.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: apply the triangle inequality to the original finite complex equation. Divide by the same actual positive growth weight and distribute the genuine finite sum. Its exact weight ratios satisfy the given original kernel bound, leaving precisely the positive linear-kernel scalar equation. -/
theorem weighted_volterra_inequality (u v : ℕ→ℂ) (G : ℕ→ℕ→ℝ) (w : ℕ→ℝ)
    (d : ℂ) (M : ℕ) {C B : ℝ} (hw:∀j≤M,0<w j)
    (hu:∀j≤M,‖u j‖≤C*w j)
    (hG:∀j≤M,∀k<j,0≤G j k ∧ G j k*w k/w j≤B*((j-k:ℕ):ℝ))
    (hv:∀j≤M,v j=u j+d*∑k∈range j,(G j k:ℂ)*v k) :
    ∀j≤M,‖v j‖/w j≤C+(‖d‖*B)*∑k∈range j,((j-k:ℕ):ℝ)*(‖v k‖/w k) := by
  -- Every norm and index is retained from the actual original equation before the scalar comparison is applied.
  intro j hj
  have hwj := hw j hj
  have hsum : ‖∑k∈range j,(G j k:ℂ)*v k‖≤∑k∈range j,G j k*‖v k‖ := by
    calc
      _ ≤ ∑k∈range j,‖(G j k:ℂ)*v k‖ := norm_sum_le _ _
      _ = _ := by
        apply sum_congr rfl
        intro k hk
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hG j hj k (mem_range.mp hk)).1]
  have hnorm : ‖v j‖≤C*w j+‖d‖*∑k∈range j,G j k*‖v k‖ := by
    rw [hv j hj]
    calc
      _ ≤ ‖u j‖+‖d*∑k∈range j,(G j k:ℂ)*v k‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul]; exact add_le_add (hu j hj) (mul_le_mul_of_nonneg_left hsum (norm_nonneg d))
  have heq : (∑k∈range j,G j k*‖v k‖)/w j=
      ∑k∈range j,(G j k*w k/w j)*(‖v k‖/w k) := by
    rw [sum_div]
    apply sum_congr rfl
    intro k hk
    have hwk := hw k (by have := mem_range.mp hk; omega)
    field_simp [hwj.ne',hwk.ne']
  have hsum' : (∑k∈range j,(G j k*w k/w j)*(‖v k‖/w k))≤
      B*∑k∈range j,((j-k:ℕ):ℝ)*(‖v k‖/w k) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have hkj := mem_range.mp hk
    have hfk : 0≤‖v k‖/w k := div_nonneg (norm_nonneg _) (hw k (by omega)).le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hG j hj k hkj).2 hfk
  have h := div_le_div_of_nonneg_right hnorm hwj.le
  rw [add_div,mul_div_cancel_right₀ _ hwj.ne',mul_div_assoc,heq] at h
  calc
    _ ≤ C+‖d‖*∑k∈range j,(G j k*w k/w j)*(‖v k‖/w k) := h
    _ ≤ C+‖d‖*(B*∑k∈range j,((j-k:ℕ):ℝ)*(‖v k‖/w k)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum' (norm_nonneg d))
    _ = _ := by ring

end
end jacobi.Finite
