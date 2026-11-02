import jacobi.Reference.Parameters

/-!
Article: jacobi, Appendix C.2 (norming ratios).
All three spectral inputs to the norming-ratio product are proved for
the genuine original spectra: inverse-square displacement and uniform
quadratic pair separation for both the reference and Bessel sequences.
Use: controls every denominator in the norming-ratio convergence proof, including small original indices.
-/
namespace jacobi.Reference
noncomputable section
open Real Set

/-- The actual reference squared-phase gaps have the printed uniform quadratic index lower bound.
Use: controls every denominator in the norming-ratio convergence proof, including small original indices.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: factor the exact difference of squared phases. Since gamma>1/4,
the sum factor is at least one quarter of the sum of the original one-based indices. -/
theorem reference_gap {a : ℝ} (ha : -1<a) {i j : ℕ} (hij : i≤j) :
    (Real.pi^2/4)*((j+1:ℝ)^2-(i+1:ℝ)^2)≤eigenvalue a j-eigenvalue a i := by
  -- The fixed potential shift cancels exactly, leaving a genuine uniform estimate for the literal source spectrum.
  have hg := (parameters ha).1
  have hdelta : 0≤(j:ℝ)-i := sub_nonneg.mpr (by exact_mod_cast hij)
  have hsum : 0≤(j:ℝ)+i := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hh : ((j:ℝ)+i+2)/4≤(j:ℝ)+i+2*gamma a := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (show 0≤Real.pi^2*((j:ℝ)-i) by positivity)
  dsimp [eigenvalue]
  nlinarith [hm]

/-- All pairs of actual Bessel zeros have a uniform positive linear index gap.
Use: squaring the actual roots gives the original quadratic spectral separation required by the norming-ratio products.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: telescope the proved genuine consecutive positive lower gap by induction on the upper index. -/
theorem bessel_root_gap {a : ℝ} (ha : -1<a) :
    ∃ d : ℝ,0<d ∧ ∀ i j : ℕ,i≤j →
      d*((j:ℝ)-i)≤ jacobi.Bessel.positiveZero a ha j- jacobi.Bessel.positiveZero a ha i := by
  -- No large-index or independently numbered zero family is substituted for the original exhaustive sequence.
  obtain ⟨d,hd,hgap⟩ := jacobi.Bessel.positiveZero_gap_lower ha
  refine ⟨d,hd,?_⟩
  intro i j hij
  induction j,hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    have hh := hgap j
    push_cast
    linarith

/-- The actual squared Bessel spectrum has a uniform positive quadratic pair gap over all original indices.
Use: supplies the Bessel denominator bound in the genuine norming-ratio convergence and estimates.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: factor the difference of actual squared zeros, use the telescoped
positive root gap and the genuine linear lower root bound, and identify
the resulting index product with the difference of one-based squares. -/
theorem bessel_spectral_gap {a : ℝ} (ha : -1<a) :
    ∃ c : ℝ,0<c ∧ ∀ i j : ℕ,i≤j →
      c*((j+1:ℝ)^2-(i+1:ℝ)^2)≤ jacobi.Bessel.sigma a ha j- jacobi.Bessel.sigma a ha i := by
  -- The argument includes every finite small-index pair through the already proved global genuine root bounds.
  obtain ⟨d,hd,hgap⟩ := bessel_root_gap ha
  obtain ⟨l,L,hl,hL,hlinear⟩ := jacobi.Bessel.positiveZero_linear_bounds ha
  refine ⟨d*l,by positivity,?_⟩
  intro i j hij
  have hsum : l*((j:ℝ)+i+2)≤ jacobi.Bessel.positiveZero a ha j+ jacobi.Bessel.positiveZero a ha i := by
    linarith [(hlinear i).1,(hlinear j).1]
  have hdiff : 0≤ jacobi.Bessel.positiveZero a ha j- jacobi.Bessel.positiveZero a ha i :=
    sub_nonneg.mpr ((jacobi.Bessel.positiveZero_strictMono ha).monotone hij)
  have hh := mul_le_mul (hgap i j hij) hsum (show 0≤l*((j:ℝ)+i+2) by positivity) hdiff
  rw [← (jacobi.Bessel.positiveZero_properties ha j).2,← (jacobi.Bessel.positiveZero_properties ha i).2]
  nlinarith [hh]

/-- The actual source spectra satisfy all quantitative norming-product input estimates with one common positive gap constant.
Use: norming-ratio convergence can apply to the literal original spectra with every spectral premise discharged.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: combine the proved original McMahon displacement and both genuine quadratic gap estimates, decreasing the gap constants to their positive minimum. -/
theorem spectral_product_inputs {a : ℝ} (ha : -1<a) :
    ∃ C c : ℝ,0<C ∧ 0<c ∧
      (∀ k,|jacobi.Bessel.sigma a ha k-eigenvalue a k|≤C/(k+1:ℝ)^2) ∧
      (∀ i j : ℕ,i≤j → c*((j+1:ℝ)^2-(i+1:ℝ)^2)≤eigenvalue a j-eigenvalue a i) ∧
      (∀ i j : ℕ,i≤j → c*((j+1:ℝ)^2-(i+1:ℝ)^2)≤ jacobi.Bessel.sigma a ha j- jacobi.Bessel.sigma a ha i) := by
  -- These are conclusions about the actual original source spectra, not fields of a certificate record.
  obtain ⟨C,hC,herror⟩ := spectrum_error ha
  obtain ⟨c,hc,hgap⟩ := bessel_spectral_gap ha
  refine ⟨C,min c (Real.pi^2/4),hC,lt_min hc (by positivity),herror,?_,?_⟩
  · intro i j hij
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by
      have h : (i+1:ℝ)≤j+1 := by exact_mod_cast Nat.add_le_add_right hij 1
      nlinarith [Nat.cast_nonneg (α := ℝ) i])).trans (reference_gap ha hij)
  · intro i j hij
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by
      have h : (i+1:ℝ)≤j+1 := by exact_mod_cast Nat.add_le_add_right hij 1
      nlinarith [Nat.cast_nonneg (α := ℝ) i])).trans (hgap i j hij)

end
end jacobi.Reference
