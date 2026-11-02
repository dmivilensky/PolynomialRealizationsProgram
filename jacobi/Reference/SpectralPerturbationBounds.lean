import jacobi.Reference.SpectralDisplacement
import jacobi.Reference.ReciprocalGaps

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The complete actual first-order perturbation row has an inverse-square
absolute sum. Its finite-index uniform bound controls the quadratic
logarithm error when the genuine norming product is linearized.
Use: spectralPerturbation_sum_bound sums the full actual epsilon row, with no omitted middle range or additional asymptotic premise.
-/
namespace jacobi.Reference
noncomputable section
open Real Finset Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original first-order spectral perturbation has its exact rational inverse-square displacement and quadratic-gap majorant.
Use: spectralPerturbation_sum_bound sums the full actual epsilon row, with no omitted middle range or additional asymptotic premise.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the numerator is the difference of the two actual McMahon displacements; reference_gap_absolute bounds its actual denominator from below. -/
theorem spectralPerturbation_majorant {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k l : ℕ,k≠l →
      |spectralPerturbation a ha k l|≤
        B*((1/(k+1:ℝ)^2+1/(l+1:ℝ)^2)/|(l+1:ℝ)^2-(k+1:ℝ)^2|) := by
  -- Actual gap positivity is established before applying the two-denominator comparison.
  obtain ⟨C,hC,herror⟩ := spectrum_error ha
  refine ⟨C/(Real.pi^2/4),by positivity,fun k l hkl => ?_⟩
  have hx : 0<(k+1:ℝ) := by positivity
  have hy : 0<(l+1:ℝ) := by positivity
  have hgap : 0< |(l+1:ℝ)^2-(k+1:ℝ)^2| := abs_pos.mpr (by
    intro h
    have he : (k:ℝ)=l := by nlinarith
    exact hkl (by exact_mod_cast he))
  have hn : |spectralDisplacement a ha l-spectralDisplacement a ha k|≤
      C/(k+1:ℝ)^2+C/(l+1:ℝ)^2 := by
    have h := (abs_sub (spectralDisplacement a ha l) (spectralDisplacement a ha k)).trans
      (add_le_add (herror l) (herror k))
    simpa only [add_comm] using h
  rw [spectralPerturbation,abs_div]
  exact (div_le_div₀ (by positivity) hn (mul_pos (by positivity : 0<Real.pi^2/4) hgap)
    (reference_gap_absolute ha k l)).trans_eq (by field_simp)

/-- The original first-order perturbation is dominated by the same two summable inverse-square rows as the actual norming logarithms.
Use: spectralPerturbation_sum_bound controls the complete row with a uniform inverse-square constant.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: apply the proved rational two-series inequality off the diagonal; the true epsilon vanishes at the omitted diagonal. -/
theorem spectralPerturbation_two_series {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k l : ℕ,
      |spectralPerturbation a ha k l|≤
        B*((2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2) := by
  obtain ⟨B,hB,hbound⟩ := spectralPerturbation_majorant ha
  refine ⟨B,hB,fun k l => ?_⟩
  by_cases h : k=l
  · subst l
    simp only [spectralPerturbation,sub_self,zero_div,abs_zero]
    dsimp [distanceMajorant]
    positivity
  · exact (hbound k l h).trans (mul_le_mul_of_nonneg_left (inverse_square_gap_majorant h) hB.le)

/-- The complete genuine first-order perturbation row converges absolutely and has a uniform inverse-square total mass.
Use: norming_log_linearization bounds the sum of all quadratic logarithm errors by O(k^-4), and the first-order mass identity then gives the strengthened rho asymptotic.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: sum the two-series majorant. The translated distance-square sum is at most twice the fixed positive p-series, giving one uniform constant for every original index. -/
theorem spectralPerturbation_sum_bound {a : ℝ} (ha : -1<a) :
    ∃ E : ℝ,0<E ∧ ∀ k : ℕ,
      Summable (fun l : ℕ => |spectralPerturbation a ha k l|) ∧
      (∑' l : ℕ,|spectralPerturbation a ha k l|)≤E/(k+1:ℝ)^2 := by
  -- Absolute convergence and its quantitative bound are proved together for the actual epsilon sequence.
  obtain ⟨B,hB,hbound⟩ := spectralPerturbation_two_series ha
  let S : ℝ := ∑' l : ℕ,1/(l+1:ℝ)^2
  have hs : Summable (fun l : ℕ => 1/(l+1:ℝ)^2) := by
    simpa only [one_pow] using jacobi.Bessel.inverse_square_majorant_summable 1
  have hS : 0<S := by
    have h := hs.le_tsum 0 (fun l _ => by positivity)
    norm_num only [Nat.cast_zero,zero_add,one_pow,div_one] at h
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) h
  refine ⟨8*B*S,by positivity,fun k => ?_⟩
  have hm : Summable (fun l : ℕ => B*((2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2)) := by
    simpa only [mul_one_div] using
      (((hs.mul_left 2).add ((distanceMajorant_summable k).mul_left 3)).div_const ((k+1:ℝ)^2)).mul_left B
  have he := hm.of_nonneg_of_le (fun _ => abs_nonneg _) (hbound k)
  refine ⟨he,(he.tsum_le_tsum (hbound k) hm).trans ?_⟩
  have hsum : (∑' l : ℕ,(2/(l+1:ℝ)^2+3*distanceMajorant k l))=
      2*S+3*(∑' l : ℕ,distanceMajorant k l) := by
    have h := (hs.mul_left 2).tsum_add ((distanceMajorant_summable k).mul_left 3)
    rw [tsum_mul_left,tsum_mul_left] at h
    simpa only [mul_one_div,S] using h
  rw [tsum_mul_left,tsum_div_const,hsum,← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (by positivity : 0<(k+1:ℝ)^2)).mpr
  have hd := distanceMajorant_tsum_le k
  change (∑' l,distanceMajorant k l)≤2*S at hd
  nlinarith [mul_le_mul_of_nonneg_left hd (show 0≤3*B by positivity)]

end
end jacobi.Reference
