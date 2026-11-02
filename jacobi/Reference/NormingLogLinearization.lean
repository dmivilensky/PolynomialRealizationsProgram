import jacobi.Reference.SpectralPerturbationBounds
import jacobi.Reference.NormingRemainders

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The logarithm of the actual convergent norming product differs from
minus the complete original first-order perturbation sum by O(k^-4).
Every logarithm remainder is bounded and summed for the true factors.
Use: norming_log_linearization identifies its summed Taylor error with the same original rho_k used in the GL kernel.
-/
namespace jacobi.Reference
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The real logarithm of the actual positive norming product is the genuinely convergent sum of its original factor logarithms.
Use: norming_log_linearization identifies its summed Taylor error with the same original rho_k used in the GL kernel.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: use the proved positive-factor exponential product identity and the actual summability of the factor logarithms. -/
theorem normingRatio_log_tsum {a : ℝ} (ha : -1<a) (k : ℕ) :
    Real.log (normingRatio a ha k)=∑' l : ℕ,Real.log (normingFactor a ha k l) := by
  rw [normingRatio,← Real.rexp_tsum_eq_tprod (normingFactor_pos ha k)
    (normingFactor_log_summable ha k),Real.log_exp]

/-- The actual product logarithm has the complete first-order spectral expansion with a uniform inverse-fourth error beyond one proved finite threshold.
Use: normingRatio_asymptotic combines this logarithm remainder with the genuine displacement-mass identity and the exponential remainder.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the complete epsilon row has absolute sum at most E/(k+1)^2, hence every actual factor is in the half-unit Taylor range past one fixed threshold. Sum the quadratic errors using abs(epsilon_l)^2<=E/(k+1)^2*abs(epsilon_l). -/
theorem norming_log_linearization {a : ℝ} (ha : -1<a) :
    ∃ L : ℝ,0<L ∧ ∃ M : ℕ,∀ k : ℕ,M≤k →
      |Real.log (normingRatio a ha k)+(∑' l : ℕ,spectralPerturbation a ha k l)|≤L/(k+1:ℝ)^4 := by
  -- The Taylor range and the error constant are conclusions for the complete original row, uniformly in all its columns.
  obtain ⟨E,hE,hbound⟩ := spectralPerturbation_sum_bound ha
  obtain ⟨M,hM⟩ := exists_nat_gt (2*E)
  refine ⟨2*E^2,by positivity,M,fun k hk => ?_⟩
  have hkpos : 0<(k+1:ℝ) := by positivity
  have hMk : (M:ℝ)≤k := by exact_mod_cast hk
  have hsmall : E/(k+1:ℝ)^2≤1/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hkpos)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hpoint (l : ℕ) : |spectralPerturbation a ha k l|≤E/(k+1:ℝ)^2 :=
    ((hbound k).1.le_tsum l (fun _ _ => abs_nonneg _)).trans (hbound k).2
  have herr (l : ℕ) : |Real.log (normingFactor a ha k l)+spectralPerturbation a ha k l|≤
      (2*(E/(k+1:ℝ)^2))*|spectralPerturbation a ha k l| := by
    rw [normingFactor_perturbation ha,Real.log_inv,
      show -Real.log (1+spectralPerturbation a ha k l)+spectralPerturbation a ha k l=
        -(Real.log (1+spectralPerturbation a ha k l)-spectralPerturbation a ha k l) by ring,abs_neg]
    have hh := log_one_add_quadratic ((hpoint l).trans hsmall)
    have hs := mul_le_mul_of_nonneg_right (hpoint l) (abs_nonneg (spectralPerturbation a ha k l))
    rw [← sq_abs] at hh
    nlinarith
  have hlogs := normingFactor_log_summable ha k
  have hsum := hlogs.add (hbound k).1.of_abs
  have hmajor := (hbound k).1.mul_left (2*(E/(k+1:ℝ)^2))
  rw [normingRatio_log_tsum ha,← hlogs.tsum_add (hbound k).1.of_abs]
  have hnorm := norm_tsum_le_tsum_norm hsum.norm
  simp only [Real.norm_eq_abs] at hnorm
  apply hnorm.trans ((hsum.abs.tsum_le_tsum herr hmajor).trans ?_)
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (hbound k).2 (by positivity)).trans_eq (by field_simp [hkpos.ne'])

end
end jacobi.Reference
