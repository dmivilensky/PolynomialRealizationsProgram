import jacobi.Finite.WeightedVolterraInequality

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
A positive weighted linear kernel bounds the genuine finite complex
source sum. This is the error estimate, before inserting the actual
support wave and its already proved global cosh bound.
Use: weighted_kernel_sum_bound proves the support wave's actual error from its top-node solution.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- A weighted linear kernel controls its finite complex source sum by the weighted source norms.
Use: weighted_kernel_sum_bound proves the support wave's actual error from its top-node solution.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the finite triangle inequality bounds the complex sum; multiplication and division by the same positive weights expose exactly the stated linear kernel bound. -/
theorem weighted_kernel_norm_sum (v : ℕ→ℂ) (G w : ℕ→ℝ) (M : ℕ) {W B : ℝ}
    (hW:0<W) (hw:∀j<M,0<w j)
    (hG:∀j<M,0≤G j ∧ G j*w j/W≤B*((M-j:ℕ):ℝ)) :
    ‖∑j∈range M,(G j:ℂ)*v j‖/W≤
      B*∑j∈range M,((M-j:ℕ):ℝ)*(‖v j‖/w j) := by
  -- The same source values are retained while the true positive growth weights cancel.
  calc
    _ ≤ (∑j∈range M,‖(G j:ℂ)*v j‖)/W :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hW.le
    _ = ∑j∈range M,(G j*w j/W)*(‖v j‖/w j) := by
      rw [sum_div]
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hG j hj').1]
      field_simp [hW.ne',(hw j hj').ne']
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (hG j (mem_range.mp hj)).2 (div_nonneg (norm_nonneg _) (hw j (mem_range.mp hj)).le)

/-- A uniformly weighted bounded complex source has a quadratic finite Volterra bound.
Use: naturalWave_difference multiplies this actual finite source estimate by the original spectral displacement and inserts its global cosh majorant.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: apply the weighted kernel estimate, bound each source norm by L and each integer distance by M+1, and count the M source terms. -/
theorem weighted_kernel_sum_bound (v : ℕ→ℂ) (G w : ℕ→ℝ) (M : ℕ) {W B L : ℝ}
    (hW:0<W) (hB:0≤B) (hL:0≤L) (hw:∀j<M,0<w j)
    (hG:∀j<M,0≤G j ∧ G j*w j/W≤B*((M-j:ℕ):ℝ))
    (hv:∀j<M,‖v j‖≤L*w j) :
    ‖∑j∈range M,(G j:ℂ)*v j‖≤B*L*((M:ℝ)+1)^2*W := by
  -- A coarse count suffices here because the factorial precision is already supplied by the global wave bound.
  have hs : (∑j∈range M,((M-j:ℕ):ℝ)*(‖v j‖/w j))≤L*((M:ℝ)+1)^2 := by
    calc
      _ ≤ ∑_j∈range M,((M:ℝ)+1)*L := by
        apply sum_le_sum
        intro j hj
        have hj' := mem_range.mp hj
        have hdist : ((M-j:ℕ):ℝ)≤(M:ℝ)+1 := by exact_mod_cast (show M-j≤M+1 by omega)
        exact mul_le_mul hdist ((div_le_iff₀ (hw j hj')).mpr (hv j hj'))
          (div_nonneg (norm_nonneg _) (hw j hj').le) (by positivity)
      _ = (M:ℝ)*(((M:ℝ)+1)*L) := by simp
      _ ≤ _ := by nlinarith
  have h := (weighted_kernel_norm_sum v G w M hW hw hG).trans (mul_le_mul_of_nonneg_left hs hB)
  exact (div_le_iff₀ hW).mp (by simpa only [mul_assoc] using h)

end
end jacobi.Finite
