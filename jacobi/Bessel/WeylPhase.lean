import jacobi.Jacobi.FrequencyComparison

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The exact leading numbered phase is derived from actual symmetric Jacobi
middle zeros and singular Sturm comparison. No large-argument Bessel
phase, asymptotic zero indexing or independent second solution is assumed.
This first-order bound fixes the phase constant for the later McMahon refinement.
Use: fixes the precise indexed phase constant before refining the cubic McMahon remainder.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter jacobi.Jacobi
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual leading Bessel zero phase in the article's zero-based indexing.
Use: fixes the precise indexed phase constant before refining the cubic McMahon remainder.
Article: jacobi, Proposition B.1.
-/
def phaseGrid (a : ℝ) (k : ℕ) : ℝ := Real.pi*((k:ℝ)+a/2+3/4)

/-- The indexed leading phase is exactly the symmetric odd-degree Jacobi middle frequency times pi/2.
Use: determines the genuine Bessel phase by a known original finite zero, rather than by an assumed asymptotic phase formula.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: substitute the literal original Jacobi frequency and simplify the natural-degree casts. -/
theorem phaseGrid_frequency (a : ℝ) (k : ℕ) :
    phaseGrid a k=(Real.pi/2)*frequency a a (2*k+1) := by
  unfold phaseGrid frequency
  push_cast
  ring

/-- The actual leading canonical phase is positive throughout the original Bessel order range.
Use: division by the phase and conversion of the squared-zero bound to the original zero bound are legitimate.
Article: jacobi, Proposition B.1.
Proof: the first phase offset alpha/2+3/4 is strictly above one quarter. -/
theorem phaseGrid_pos {a : ℝ} (ha : -1<a) (k : ℕ) : 0<phaseGrid a k := by
  unfold phaseGrid
  apply mul_pos Real.pi_pos
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  linarith

/-- The actual squared Bessel zeros differ from their precise indexed leading phase squares by one uniform finite constant.
Use: fixes the exact genuine large-zero phase with no integer-index ambiguity before the McMahon remainder is refined.
Article: jacobi, Proposition B.1.
Proof: compare the true symmetric odd-degree Jacobi equation with Bessel
frequencies sqrt(N^2+C+1) and sqrt(N^2-C-1), using the genuinely bounded
regular potential and the actual zero Wronskian. Its exact middle angle
is pi/2. Numbered Sturm comparison gives both squared-zero bounds. When
the lower squared frequency is nonpositive, positivity already supplies
the needed lower estimate. The constant is uniform in every actual index. -/
theorem sigma_phase_bounded {a : ℝ} (ha : -1<a) :
    ∃ M : ℝ,0<M ∧ ∀ k,|sigma a ha k-(phaseGrid a k)^2|≤M := by
  -- All comparison hypotheses below are discharged for the original Jacobi and Bessel functions.
  obtain ⟨C,hC,hbound⟩ := regularPotential_C1_bound a a
  let M : ℝ := (Real.pi/2)^2*(C+1)
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro k
  let n := 2*k+1
  let N := frequency a a n
  have hn : k<n := by dsimp [n]; omega
  have hN : 0<N := frequency_pos ha ha (by dsimp [n]; omega)
  have hgrid : phaseGrid a k=(Real.pi/2)*N := phaseGrid_frequency a k
  have hmid : finiteAngleAt a a ha ha n k=Real.pi/2 := by
    rw [finiteAngleAt_eq ha ha hn]
    exact symmetric_middle_angle ha k
  have hpotbound : ∀ x∈Ioo 0 (Real.pi/2),|regularPotential a a x|≤C := by
    intro x hx
    exact (hbound x ⟨hx.1.le,by linarith [hx.2,Real.pi_pos]⟩).1
  have hR : Real.pi/2<Real.pi := by linarith [Real.pi_pos]
  have hpi : 0<Real.pi/2 := by positivity
  let U : ℝ := √(N^2+C+1)
  have hUp : 0<U := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg N])
  have hU2 : U^2=N^2+C+1 := Real.sq_sqrt (by nlinarith [sq_nonneg N])
  have hupper := bessel_zero_lt_angle ha ha hUp hR hn hmid.le
    (fun x hx => by
      change N^2+regularPotential a a x<U^2
      rw [hU2]
      linarith [(le_abs_self (regularPotential a a x)).trans (hpotbound x hx)]) k le_rfl
  rw [hmid] at hupper
  have hupperJ : positiveZero a ha k<(Real.pi/2)*U := (div_lt_iff₀ hUp).mp hupper
  have hu : sigma a ha k≤(phaseGrid a k)^2+M := by
    rw [← (positiveZero_properties ha k).2]
    calc
      _ ≤ ((Real.pi/2)*U)^2 := (sq_le_sq₀ (positiveZero_properties ha k).1.le (mul_pos hpi hUp).le).mpr hupperJ.le
      _ = (phaseGrid a k)^2+M := by rw [mul_pow,hU2,hgrid]; dsimp [M]; ring
  have hl : (phaseGrid a k)^2-M≤sigma a ha k := by
    by_cases hL : 0<N^2-C-1
    · let L : ℝ := √(N^2-C-1)
      have hLp : 0<L := Real.sqrt_pos.mpr hL
      have hL2 : L^2=N^2-C-1 := Real.sq_sqrt hL.le
      have hlow : Real.pi/2<scaledZero a ha L k := by
        by_contra hnot
        have hzero : scaledZero a ha L k≤Real.pi/2 := not_lt.mp hnot
        have hh := angle_lt_bessel_zero ha ha hLp hR hn hzero
          (fun x hx => by
            change L^2<N^2+regularPotential a a x
            rw [hL2]
            have hb := (abs_le.mp (hpotbound x hx)).1
            linarith) k le_rfl
        rw [hmid] at hh
        linarith
      have hlowJ : (Real.pi/2)*L<positiveZero a ha k := (lt_div_iff₀ hLp).mp hlow
      rw [← (positiveZero_properties ha k).2]
      calc
        _ = ((Real.pi/2)*L)^2 := by rw [mul_pow,hL2,hgrid]; dsimp [M]; ring
        _ ≤ _ := (sq_le_sq₀ (mul_pos hpi hLp).le (positiveZero_properties ha k).1.le).mpr hlowJ.le
    · have hNl : N^2≤C+1 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hNl (sq_nonneg (Real.pi/2))
      rw [hgrid,mul_pow]
      dsimp [M]
      nlinarith [spectralZero_pos ha (sigma_mem ha k)]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The genuine indexed Bessel zeros have the exact leading phase with a uniform inverse-index error.
Use: fixes the actual continuous phase constant at infinity before the cubic McMahon remainder is established.
Article: jacobi, Lemma E.1.
Proof: factor the proved actual difference of squares. Positivity of the
original zero and phase bounds the denominator below by the phase, which
is at least pi*(k+1)/4 throughout alpha>-1. -/
theorem positiveZero_phase_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k,|positiveZero a ha k-phaseGrid a k|≤C/(k+1:ℝ) := by
  -- The finite symmetric comparison has already fixed the source phase offset, so no phase-index ambiguity is absorbed into this error.
  obtain ⟨M,hM,hbound⟩ := sigma_phase_bounded ha
  refine ⟨4*M/Real.pi,by positivity,?_⟩
  intro k
  have hj := (positiveZero_properties ha k).1
  have hv := phaseGrid_pos ha k
  have hsq := hbound k
  rw [← (positiveZero_properties ha k).2,
    show (positiveZero a ha k)^2-(phaseGrid a k)^2=
      (positiveZero a ha k-phaseGrid a k)*(positiveZero a ha k+phaseGrid a k) by ring,
    abs_mul,abs_of_pos (add_pos hj hv)] at hsq
  have hlin : |positiveZero a ha k-phaseGrid a k| * phaseGrid a k≤M := by
    have hh := mul_le_mul_of_nonneg_left (show phaseGrid a k≤positiveZero a ha k+phaseGrid a k by linarith) (abs_nonneg (positiveZero a ha k-phaseGrid a k))
    exact hh.trans hsq
  have hlo : (Real.pi/4)*(k+1:ℝ)≤phaseGrid a k := by
    have hk : (0:ℝ)≤k := Nat.cast_nonneg k
    have hb : ((k:ℝ)+1)/4≤(k:ℝ)+a/2+3/4 := by linarith
    have hh := mul_le_mul_of_nonneg_left hb Real.pi_pos.le
    dsimp [phaseGrid]
    nlinarith only [hh]
  calc
    _ ≤ M/phaseGrid a k := (le_div_iff₀ hv).mpr hlin
    _ ≤ M/((Real.pi/4)*(k+1:ℝ)) := div_le_div_of_nonneg_left hM.le (by positivity) hlo
    _ = _ := by field_simp

/-- The original indexed Bessel zero minus its exact leading phase tends to zero.
Use: identifies the genuine limiting Pruefer phase constant, which the McMahon integration argument needs to evaluate its remainder.
Article: jacobi, Proposition B.1.
Proof: squeeze the actual absolute error by the proved constant multiple
of 1/(k+1), then pass from its real norm to the original zero difference. -/
theorem positiveZero_phase_tendsto {a : ℝ} (ha : -1<a) :
    Tendsto (fun k : ℕ => positiveZero a ha k-phaseGrid a k) atTop (𝓝 0) := by
  -- The error bound is unconditional for the original exhaustive Bessel zero list.
  obtain ⟨C,_,hC⟩ := positiveZero_phase_bound ha
  have hi : Tendsto (fun k : ℕ => C/(k+1:ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).const_mul C
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,mul_zero,mul_one_div] using h
  have ht := squeeze_zero (fun k => abs_nonneg (positiveZero a ha k-phaseGrid a k)) hC hi
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using ht

end
end jacobi.Bessel
