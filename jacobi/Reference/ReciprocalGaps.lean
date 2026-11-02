import jacobi.Reference.HarmonicGaps
import jacobi.Reference.SpectralGaps

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The complete row of reciprocal actual reference gaps has the sharp
logarithmic inverse-index bound, including its omitted diagonal.
The original common quadratic spectral gap estimate is reused.
Use: spectralPerturbation_majorant and spectral_reciprocal_gap_bound control all denominators in the strengthened norming asymptotic.
-/
namespace jacobi.Reference
noncomputable section
open Real Finset Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual reference gap dominates the absolute squared-integer gap, with the original positive pi constant.
Use: spectralPerturbation_majorant and spectral_reciprocal_gap_bound control all denominators in the strengthened norming asymptotic.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: order the original indices, apply reference_gap, and reverse both differences if necessary. -/
theorem reference_gap_absolute {a : ℝ} (ha : -1<a) (k l : ℕ) :
    (Real.pi^2/4)*|(l+1:ℝ)^2-(k+1:ℝ)^2|≤|eigenvalue a l-eigenvalue a k| := by
  -- Both signs are fixed by the genuine increasing reference spectrum.
  rcases le_total k l with h | h
  · have he := reference_gap ha h
    have hnat : (k+1:ℝ)≤l+1 := by exact_mod_cast Nat.add_le_add_right h 1
    rw [abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) k]),
      abs_of_nonneg (sub_nonneg.mpr ((eigenvalue_strictMono ha).monotone h))]
    exact he
  · have he := reference_gap ha h
    have hnat : (l+1:ℝ)≤k+1 := by exact_mod_cast Nat.add_le_add_right h 1
    rw [abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) l]),
      abs_of_nonpos (sub_nonpos.mpr ((eigenvalue_strictMono ha).monotone h))]
    linarith

/-- The reciprocal actual reference gap is dominated by the genuine integer quadratic-gap row at every pair of indices.
Use: spectral_reciprocal_gap_bound transfers the complete harmonic row estimate to the same tau denominators as the original norming factors.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: off the diagonal both denominators are positive and reference_gap_absolute can be inverted; on the diagonal both actual reciprocals are zero. -/
theorem reference_gap_reciprocal_majorant {a : ℝ} (ha : -1<a) (k l : ℕ) :
    1/|eigenvalue a l-eigenvalue a k|≤(4/Real.pi^2)*quadraticGapRow k l := by
  -- The diagonal is zero; only strictly positive off-diagonal gap estimates are inverted.
  by_cases hkl : k=l
  · subst l
    simp [quadraticGapRow]
  · have hn : (l+1:ℝ)≠k+1 := by
      intro h
      apply hkl
      exact_mod_cast (by linarith : (k:ℝ)=l)
    have hgap : 0< |(l+1:ℝ)^2-(k+1:ℝ)^2| := abs_pos.mpr (by
      intro h
      have hx : 0<(k+1:ℝ) := by positivity
      have hy : 0<(l+1:ℝ) := by positivity
      exact hn (by nlinarith))
    have hpi : 0<Real.pi^2/4 := by positivity
    have hh := one_div_le_one_div_of_le (mul_pos hpi hgap) (reference_gap_absolute ha k l)
    exact hh.trans_eq (by dsimp [quadraticGapRow]; field_simp)

/-- The complete genuine reciprocal reference-gap row is summable and bounded by a constant times log(k)/k at every original index.
Use: the exact first-order spectral perturbation identity gives the O(k^-3 log k) norming-ratio remainder with the true displacement mass.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the actual reciprocal gaps are dominated by the proved summable quadratic-gap row, whose complete sum has its harmonic logarithmic bound. -/
theorem spectral_reciprocal_gap_bound {a : ℝ} (ha : -1<a) :
    ∃ G : ℝ,0<G ∧ ∀ k : ℕ,
      Summable (fun l : ℕ => 1/|eigenvalue a l-eigenvalue a k|) ∧
      (∑' l : ℕ,1/|eigenvalue a l-eigenvalue a k|)≤
        G*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ) := by
  -- Convergence is proved for the complete original row before taking its sum.
  refine ⟨8/Real.pi^2,by positivity,fun k => ?_⟩
  have hm := (quadraticGapRow_summable k).mul_left (4/Real.pi^2)
  have hs := hm.of_nonneg_of_le (fun _ => by positivity) (reference_gap_reciprocal_majorant ha k)
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∑' l : ℕ,(4/Real.pi^2)*quadraticGapRow k l :=
      hs.tsum_le_tsum (reference_gap_reciprocal_majorant ha k) hm
    _ = (4/Real.pi^2)*(∑' l : ℕ,quadraticGapRow k l) := tsum_mul_left
    _ ≤ (4/Real.pi^2)*(2*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ)) :=
      mul_le_mul_of_nonneg_left (quadratic_gap_row_bound k) (by positivity)
    _ = _ := by ring

end
end jacobi.Reference
