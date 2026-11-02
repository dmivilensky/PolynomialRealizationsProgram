import jacobi.Reference.HarmonicSums

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The complete reciprocal quadratic-gap row is summable and bounded
by a harmonic number divided by the original positive index. This
provides the logarithmic loss in the sharpened norming asymptotic.
Use: quadratic_gap_row_bound controls the genuine spectral reciprocal-gap sum in the strengthened norming-ratio asymptotic.
-/
namespace jacobi.Reference
noncomputable section
open Real Finset Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual reciprocal squared-integer gap, with its omitted diagonal equal to zero by totalized division.
Use: quadratic_gap_row_bound controls the genuine spectral reciprocal-gap sum in the strengthened norming-ratio asymptotic.
Article: jacobi, Appendix C.2 (norming ratios).
-/
def quadraticGapRow (k l : ℕ) : ℝ := 1/|(l+1:ℝ)^2-(k+1:ℝ)^2|

/-- The original right quadratic-gap tail is exactly the positive reciprocal-product series.
Use: quadratic_gap_right_hasSum evaluates its complete sum using the finite harmonic telescoping identity.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: factor the positive difference of the actual two integer squares after translating l=k+1+j. -/
theorem quadratic_gap_right (k j : ℕ) :
    quadraticGapRow k (j+(k+1))=1/((j+1:ℝ)*(j+2*(k+1)+1:ℝ)) := by
  have he : ((j+(k+1):ℕ)+1:ℝ)^2-(k+1:ℝ)^2=(j+1:ℝ)*(j+2*(k+1)+1:ℝ) := by
    push_cast
    ring
  rw [quadraticGapRow,he,abs_of_pos (by positivity)]

/-- The whole genuine right quadratic-gap tail has its exact harmonic sum.
Use: quadraticGapRow_summable and quadratic_gap_row_bound retain the entire infinite tail of the reciprocal spectral-gap estimate.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the exact factorization identifies the tail with reciprocal_product_hasSum at shift 2*(k+1). -/
theorem quadratic_gap_right_hasSum (k : ℕ) :
    HasSum (fun j : ℕ => quadraticGapRow k (j+(k+1)))
      (harmonicSum (2*(k+1))/(2*(k+1):ℝ)) := by
  have h := reciprocal_product_hasSum (show 0<2*(k+1) by omega)
  simpa only [quadratic_gap_right,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using h

/-- The actual reciprocal quadratic-gap row is absolutely summable at every original index.
Use: all subsequent sums of first-order spectral perturbations and their remainders have genuine convergence evidence.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: translate past the finite prefix and the omitted diagonal, then use the exact convergent right-tail series. -/
theorem quadraticGapRow_summable (k : ℕ) : Summable (quadraticGapRow k) :=
  (summable_nat_add_iff (k+1)).mp (quadratic_gap_right_hasSum k).summable

/-- Each genuine left reciprocal quadratic gap is bounded by its reflected reciprocal distance divided by the positive original index.
Use: quadratic_gap_prefix_bound sums the finite left part of the same complete gap row.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the factored absolute gap is (k-l)*(k+l+2), whose second factor is at least k+1. -/
theorem quadratic_gap_left {k l : ℕ} (hkl : l<k) :
    quadraticGapRow k l≤(1/((k:ℝ)-l))/(k+1:ℝ) := by
  -- Strict index order supplies both positive denominator factors before division.
  have hd : 0<(k:ℝ)-l := sub_pos.mpr (by exact_mod_cast hkl)
  have hs : 0<(k:ℝ)+(l:ℝ)+2 := by positivity
  have he : (l+1:ℝ)^2-(k+1:ℝ)^2= -(((k:ℝ)-l)*((k:ℝ)+(l:ℝ)+2)) := by ring
  rw [quadraticGapRow,he,abs_neg,abs_of_pos (mul_pos hd hs),div_div]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) l]

/-- The full finite left quadratic-gap prefix is bounded by the genuine harmonic prefix divided by its positive original index.
Use: quadratic_gap_row_bound combines this bound with the exact complete right-tail value.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: sum the pointwise left-gap estimate and reverse the finite reciprocal-distance range to the original harmonic sum. -/
theorem quadratic_gap_prefix_bound (k : ℕ) :
    (∑ l∈range k,quadraticGapRow k l)≤harmonicSum k/(k+1:ℝ) := by
  -- Reflection is exact on the finite prefix and does not introduce a diagonal term.
  calc
    _ ≤ ∑ l∈range k,(1/((k:ℝ)-l))/(k+1:ℝ) :=
      Finset.sum_le_sum (fun l hl => quadratic_gap_left (mem_range.mp hl))
    _ = _ := by
      rw [← Finset.sum_div,← Finset.sum_range_reflect (fun l : ℕ => 1/((k:ℝ)-l)) k]
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      have hlk := mem_range.mp hl
      have he : ((k-1-l:ℕ):ℝ)=(k:ℝ)-1-l := by
        rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
      rw [he]
      congr 1
      ring

/-- The complete genuine reciprocal quadratic-gap row has its logarithmic inverse-index bound, uniformly over every original index.
Use: spectral_reciprocal_gap_bound controls the exact first-order norming correction and yields the printed O(k^-3 log k) remainder.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the finite prefix is at most H_k/(k+1), the infinite tail is exactly H_(2k+2)/(2k+2), and both are bounded by twice the common harmonic term; apply the community logarithmic estimate. -/
theorem quadratic_gap_row_bound (k : ℕ) :
    (∑' l : ℕ,quadraticGapRow k l)≤
      2*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ) := by
  -- The actual whole row is decomposed into a finite prefix, its zero diagonal, and its complete right tail.
  have hk : 0<(k+1:ℝ) := by positivity
  have hH : 0≤harmonicSum (2*(k+1)) := Finset.sum_nonneg (fun _ _ => by positivity)
  rw [← (quadraticGapRow_summable k).sum_add_tsum_nat_add (k+1),Finset.sum_range_succ]
  rw [show quadraticGapRow k k=0 by simp [quadraticGapRow],add_zero,
    (quadratic_gap_right_hasSum k).tsum_eq]
  have hmono := harmonicSum_mono (show k≤2*(k+1) by omega)
  have hhalf : harmonicSum (2*(k+1))/(2*(k+1):ℝ)≤harmonicSum (2*(k+1))/(k+1:ℝ) :=
    div_le_div_of_nonneg_left hH hk (by linarith)
  have hp := (quadratic_gap_prefix_bound k).trans (div_le_div_of_nonneg_right hmono hk.le)
  calc
    _ ≤ 2*harmonicSum (2*(k+1))/(k+1:ℝ) := (add_le_add hp hhalf).trans_eq (by ring)
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using harmonicSum_log_bound (2*(k+1))) (by norm_num)) hk.le

end
end jacobi.Reference
