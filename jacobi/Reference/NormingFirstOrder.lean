import jacobi.Reference.SpectralPerturbationBounds

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The complete first-order perturbation sum has the genuine leading
coefficient minus s/varpi_k^2. One exact summand identity reduces its
remainder to the proved reciprocal-gap row, retaining O(k^-3 log k).
Use: spectralPerturbation_mass_identity isolates the actual displacement mass in the first-order norming correction.
-/
namespace jacobi.Reference
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original reference gap is exactly the difference of its genuine squared phases.
Use: spectralPerturbation_mass_identity isolates the actual displacement mass in the first-order norming correction.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the common original potential correction cancels in the two exact reference eigenvalue formulas. -/
theorem reference_gap_phase (a : ℝ) (k l : ℕ) :
    eigenvalue a l-eigenvalue a k=(jacobi.Bessel.phaseGrid a l)^2-(jacobi.Bessel.phaseGrid a k)^2 := by
  rw [eigenvalue_eq,eigenvalue_eq]
  ring

/-- The actual first-order perturbation plus its displacement-mass summand has an exact weighted-gap remainder off the omitted diagonal.
Use: spectralPerturbation_mass_majorant sums this identity against the genuine bounded weighted displacements and the harmonic reciprocal-gap row.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: substitute the exact squared-phase gap and clear its nonzero denominator and the positive squared phase. -/
theorem spectralPerturbation_mass_identity {a : ℝ} (ha : -1<a) {k l : ℕ} (hkl : l≠k) :
    spectralPerturbation a ha k l+spectralDisplacement a ha l/(jacobi.Bessel.phaseGrid a k)^2=
      (spectralDisplacement a ha l*(jacobi.Bessel.phaseGrid a l)^2)/
        ((jacobi.Bessel.phaseGrid a k)^2*(eigenvalue a l-eigenvalue a k))-
      spectralDisplacement a ha k/(eigenvalue a l-eigenvalue a k) := by
  have hgap : eigenvalue a l-eigenvalue a k≠0 := sub_ne_zero.mpr
    (fun h => hkl ((eigenvalue_strictMono ha).injective h))
  rw [reference_gap_phase a k l] at hgap
  rw [spectralPerturbation,reference_gap_phase a k l]
  field_simp [hgap,(jacobi.Bessel.phaseGrid_pos ha k).ne']
  ring

/-- Every actual first-order mass-correction summand has a uniform reciprocal-gap majorant plus its single omitted-diagonal correction.
Use: norming_first_order_bound sums the original correction row and gives the exact O(k^-3 log k) remainder with the genuine displacementMass.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the exact weighted-gap identity bounds off-diagonal terms by (B/varpi_k^2+abs(delta_k))/abs(tau_l-tau_k). The true diagonal contributes only abs(delta_k)/varpi_k^2. All coefficients obey the proved inverse-square bounds. -/
theorem spectralPerturbation_mass_majorant {a : ℝ} (ha : -1<a) :
    ∃ A T : ℝ,0<A ∧ 0<T ∧ ∀ k l : ℕ,
      |spectralPerturbation a ha k l+spectralDisplacement a ha l/(jacobi.Bessel.phaseGrid a k)^2|≤
        ((A/(k+1:ℝ)^2)*(1/|eigenvalue a l-eigenvalue a k|))+
          (if l=k then T/(k+1:ℝ)^4 else 0) := by
  -- The diagonal is kept explicitly, rather than being lost when the original off-diagonal identity is summed.
  obtain ⟨B,D,hB,hD,hphase⟩ := displacement_phase_bounds ha
  obtain ⟨C,hC,herror⟩ := spectrum_error ha
  refine ⟨B*D+C,C*D,by positivity,by positivity,fun k l => ?_⟩
  have hkpos : 0<(k+1:ℝ) := by positivity
  have hcoeff : B/(jacobi.Bessel.phaseGrid a k)^2+|spectralDisplacement a ha k|≤
      (B*D+C)/(k+1:ℝ)^2 := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hphase k).2 hB.le) (herror k)
    calc
      _ = B*(1/(jacobi.Bessel.phaseGrid a k)^2)+|spectralDisplacement a ha k| := by ring
      _ ≤ B*(D/(k+1:ℝ)^2)+C/(k+1:ℝ)^2 := hh
      _ = _ := by ring
  by_cases h : l=k
  · subst l
    simp only [spectralPerturbation,sub_self,zero_add,abs_zero,div_zero,mul_zero,ite_true]
    rw [abs_div,abs_of_nonneg (sq_nonneg (jacobi.Bessel.phaseGrid a k))]
    have hh := mul_le_mul (herror k) (hphase k).2 (by positivity) (by positivity)
    exact (show |spectralDisplacement a ha k|/(jacobi.Bessel.phaseGrid a k)^2=
      |spectralDisplacement a ha k| * (1/(jacobi.Bessel.phaseGrid a k)^2) by ring).trans_le
        (hh.trans_eq (by field_simp [hkpos.ne']))
  · rw [spectralPerturbation_mass_identity ha h,ite_eq_right h,add_zero]
    calc
      _ ≤ |(spectralDisplacement a ha l*(jacobi.Bessel.phaseGrid a l)^2)/
          ((jacobi.Bessel.phaseGrid a k)^2*(eigenvalue a l-eigenvalue a k))|+
          |spectralDisplacement a ha k/(eigenvalue a l-eigenvalue a k)| := abs_sub _ _
      _ = (|spectralDisplacement a ha l| * (jacobi.Bessel.phaseGrid a l)^2)/
          ((jacobi.Bessel.phaseGrid a k)^2*|eigenvalue a l-eigenvalue a k|)+
          |spectralDisplacement a ha k|/|eigenvalue a l-eigenvalue a k| := by
        simp only [abs_div,abs_mul,abs_pow,sq_abs]
      _ ≤ B/((jacobi.Bessel.phaseGrid a k)^2*|eigenvalue a l-eigenvalue a k|)+
          |spectralDisplacement a ha k|/|eigenvalue a l-eigenvalue a k| :=
        add_le_add (div_le_div_of_nonneg_right (hphase l).1 (by positivity)) le_rfl
      _ = (B/(jacobi.Bessel.phaseGrid a k)^2+|spectralDisplacement a ha k|)*
          (1/|eigenvalue a l-eigenvalue a k|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- The genuine complete first-order norming correction equals minus the actual displacement mass over the squared reference phase, with the printed logarithmic inverse-cubic error.
Use: normingRatio_asymptotic combines this theorem with the true product logarithm linearization and exponential remainder; the same displacementMass defines F-flat.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: sum the exact correction row and its proved summable majorant. The complete reciprocal-gap row contributes O(log(k)/k), and the single diagonal remainder is O(k^-4), which the same bound absorbs. -/
theorem norming_first_order_bound {a : ℝ} (ha : -1<a) :
    ∃ Q : ℝ,0<Q ∧ ∀ k : ℕ,
      |(∑' l : ℕ,spectralPerturbation a ha k l)+displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2|≤
        Q*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ)^3 := by
  classical
  -- All infinite sums below have convergence evidence before the linear identity and comparison are applied.
  obtain ⟨A,T,hA,hT,hpoint⟩ := spectralPerturbation_mass_majorant ha
  obtain ⟨G,hG,hgap⟩ := spectral_reciprocal_gap_bound ha
  obtain ⟨E,_hE,hepsilon⟩ := spectralPerturbation_sum_bound ha
  refine ⟨A*G+T,by positivity,fun k => ?_⟩
  have hk : 0<(k+1:ℝ) := by positivity
  have hJ : 1≤1+Real.log (2*(k+1:ℝ)) := by
    have h := Real.log_nonneg (show 1≤2*(k+1:ℝ) by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    linarith
  have htheta := ((hepsilon k).1.of_abs).add ((spectralDisplacement_summable ha).of_abs.div_const ((jacobi.Bessel.phaseGrid a k)^2))
  have hm := ((hgap k).1.mul_left (A/(k+1:ℝ)^2)).add
    (hasSum_ite_eq k (T/(k+1:ℝ)^4)).summable
  have heq : (∑' l : ℕ,(spectralPerturbation a ha k l+spectralDisplacement a ha l/(jacobi.Bessel.phaseGrid a k)^2))=
      (∑' l : ℕ,spectralPerturbation a ha k l)+displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2 := by
    rw [((hepsilon k).1.of_abs).tsum_add ((spectralDisplacement_summable ha).of_abs.div_const _),tsum_div_const]
    rfl
  rw [← heq]
  have hnorm := norm_tsum_le_tsum_norm htheta.norm
  simp only [Real.norm_eq_abs] at hnorm
  apply hnorm.trans ((htheta.abs.tsum_le_tsum (hpoint k) hm).trans ?_)
  rw [(((hgap k).1.mul_left (A/(k+1:ℝ)^2))).tsum_add (hasSum_ite_eq k (T/(k+1:ℝ)^4)).summable,
    tsum_mul_left,tsum_ite_eq]
  have hdiag : T/(k+1:ℝ)^4≤T*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ)^3 := by
    have hi : 1/(k+1:ℝ)≤1+Real.log (2*(k+1:ℝ)) :=
      (one_div_le_one_div_of_le zero_lt_one (by nlinarith [Nat.cast_nonneg (α := ℝ) k])).trans (by simpa using hJ)
    exact (show T/(k+1:ℝ)^4=(T/(k+1:ℝ)^3)*(1/(k+1:ℝ)) by field_simp [hk.ne']).trans_le
      ((mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring))
  have hmain := mul_le_mul_of_nonneg_left (hgap k).2 (show 0≤A/(k+1:ℝ)^2 by positivity)
  exact (add_le_add hmain hdiag).trans_eq (by field_simp [hk.ne'])

end
end jacobi.Reference
