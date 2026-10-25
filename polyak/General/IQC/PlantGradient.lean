import polyak.General.IQC.StablePlant

/-! The zero-initial plant satisfies the genuine two-sided recurrence after
extension by zero.  Therefore the Part I gradient filter recovers exactly
the causal input, including the start and all negative indices. -/

namespace polyak.General.IQC
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]
section Recurrence
variable [NormedSpace ℝ E]

theorem stablePlant_zeroExtend_recurrence (A B beta : ℝ) {r : ℝ} (hr : r ≠ 0)
    (x : ℕ → E) (k : ℤ) :
    r • zeroExtend (stablePlant A B beta r x) (k+1) -
      A • zeroExtend (stablePlant A B beta r x) k +
      (beta/r) • zeroExtend (stablePlant A B beta r x) (k-1) = B • zeroExtend x k := by
  by_cases hk : k < 0
  · have hx : zeroExtend x k=0 := zeroExtend_neg x hk
    have hy : zeroExtend (stablePlant A B beta r x) k=0 := zeroExtend_neg _ hk
    have hym : zeroExtend (stablePlant A B beta r x) (k-1)=0 := zeroExtend_neg _ (by omega)
    have hyp : zeroExtend (stablePlant A B beta r x) (k+1)=0 := by
      by_cases hkp : k+1=0
      · rw [hkp]; exact stablePlant_zero _ _ _ _ _
      · exact zeroExtend_neg _ (by omega)
    simp [hx,hy,hym,hyp]
  · lift k to ℕ using (le_of_not_gt hk)
    cases k with
    | zero =>
      simp only [Int.natCast_zero,zero_add,zero_sub]
      simp [zeroExtend,stablePlant_one,smul_smul]
      congr 1
      field_simp
    | succ n =>
      have hp : (↑(n+1):ℤ)+1=(↑(n+2):ℤ) := by omega
      have hm : (↑(n+1):ℤ)-1=(n:ℤ) := by omega
      rw [hp,hm,zeroExtend_nat,zeroExtend_nat,zeroExtend_nat,zeroExtend_nat,
        stablePlant_recurrence]
      simp only [smul_add,smul_sub,smul_smul]
      have hA : r*(A/r)=A := by field_simp
      have hB : r*(B/r)=B := by field_simp
      have hbeta : r*(beta/r^2)=beta/r := by field_simp
      rw [hA,hB,hbeta]
      module

end Recurrence
section Gradient
variable [InnerProductSpace ℝ E]
theorem stablePlant_gradientFilter (A B beta t : ℝ) (hB : B ≠ 0)
    (x : ℕ → E) (k : ℤ) :
    Energy.filterEval (Energy.gradientFilter A B beta t)
      (zeroExtend (stablePlant A B beta (Real.exp t) x)) k = zeroExtend x k := by
  rw [Energy.filterEval_gradient,Real.exp_neg]
  have h := stablePlant_zeroExtend_recurrence A B beta (ne_of_gt (Real.exp_pos t)) x k
  calc
    _ = (1/B) • (Real.exp t • zeroExtend (stablePlant A B beta (Real.exp t) x) (k+1) -
      A • zeroExtend (stablePlant A B beta (Real.exp t) x) k +
      (beta/Real.exp t) • zeroExtend (stablePlant A B beta (Real.exp t) x) (k-1)) := by
        simp only [smul_add,smul_sub,smul_smul]
        module
    _ = (1/B) • (B • zeroExtend x k) := by rw [h]
    _ = zeroExtend x k := by rw [smul_smul,one_div_mul_cancel hB,one_smul]

end Gradient
end
end polyak.General.IQC
