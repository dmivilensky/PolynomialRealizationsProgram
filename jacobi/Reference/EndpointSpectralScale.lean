import jacobi.Reference.EndpointEnergyDerivative
import jacobi.Reference.ZeroGreenFactor
import jacobi.Reference.BesselFrequency
import jacobi.Reference.SpectralScale
import jacobi.Reference.SpectralDisplacement

/-!
Article: jacobi, Proposition C.4.
Source: the proved original McMahon displacement and real mean-value theorem.
Use: all endpoint-sensitive spectral comparisons apply to the true finite prefix as well as the infinite tail.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- One positive linear scale bounds both genuine reference and shifted Bessel frequencies at every original spectral index.
Use: all endpoint-sensitive spectral comparisons apply to the true finite prefix as well as the infinite tail.
Article: jacobi, Proposition C.4.
Proof: the previously proved common spectral energy scale gives an eventual positive lower bound for their minimum divided by k+1. Every remaining original frequency is positive; reuse the earlier finite-prefix absorption lemma. -/
theorem spectral_frequency_lower {a : ℝ} (ha : -1<a) :
    ∃ d : ℝ,0<d ∧ ∀ k : ℕ,d*(k+1:ℝ)≤besselFrequency a ha k ∧
      d*(k+1:ℝ)≤ jacobi.Bessel.phaseGrid a k := by
  -- The finite-prefix absorption uses only actual positive original frequencies, without numerical certificates.
  obtain ⟨d,hd,hscale⟩ := spectral_energy_scale ha
  let f := fun k : ℕ => min (besselFrequency a ha k/(k+1:ℝ))
    (jacobi.Bessel.phaseGrid a k/(k+1:ℝ))
  have hf (k : ℕ) : 0<f k := lt_min
    (div_pos (besselFrequency_pos ha k) (by positivity))
    (div_pos (jacobi.Bessel.phaseGrid_pos ha k) (by positivity))
  have he : ∀ᶠ k : ℕ in atTop,d≤f k := by
    filter_upwards [hscale] with k hk
    have hn : 0<(k+1:ℝ) := by positivity
    have hdp : 0<d*(k+1:ℝ) := mul_pos hd hn
    have hB := besselFrequency_pos ha k
    have hP := jacobi.Bessel.phaseGrid_pos ha k
    have hBs := besselFrequency_sq ha k
    have hPs := reference_energy_phase a k
    apply le_min
    · apply (le_div_iff₀ hn).mpr
      nlinarith [hk.2.2]
    · apply (le_div_iff₀ hn).mpr
      nlinarith [hk.2.1]
  obtain ⟨c,hc,hall⟩ := jacobi.Bessel.positive_lower_all hf hd he
  refine ⟨c,hc,fun k => ?_⟩
  have h := hall k
  exact ⟨(le_div_iff₀ (by positivity : 0<(k+1:ℝ))).mp (le_min_iff.mp h).1,
    (le_div_iff₀ (by positivity : 0<(k+1:ℝ))).mp (le_min_iff.mp h).2⟩

/-- The genuine frequency minimum is bounded by the original index minimum under a positive linear frequency lower bound.
Use: endpoint_spectral_difference and the actual transformed spectral wave estimates share one exact physical envelope.
Article: jacobi, Proposition C.4.
Proof: the physical endpoint power is nonnegative. The inverse-frequency power decreases above d*(k+1); positive power multiplication and the factor max(1,d^-gamma) bound both components of the target minimum. -/
theorem spectral_minimum_bound {a d w t : ℝ} (ha : -1<a) (hd : 0<d)
    (ht : 0≤t) (k : ℕ) (hw : d*(k+1:ℝ)≤w) :
    min (t^(gamma a)) (w^(-gamma a))≤
      max 1 (d^(-gamma a))*min (t^(gamma a)) ((k+1:ℝ)^(-gamma a)) := by
  -- The same bound applies to arbitrarily small positive original frequencies.
  have hn : 0<(k+1:ℝ) := by positivity
  have hD : 0≤max 1 (d^(-gamma a)) := le_trans zero_le_one (le_max_left _ _)
  rw [mul_min_of_nonneg (t^(gamma a)) ((k+1:ℝ)^(-gamma a)) hD]
  refine le_min ?_ ?_
  · exact (min_le_left _ _).trans (le_mul_of_one_le_left (Real.rpow_nonneg ht _) (le_max_left _ _))
  · have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hd hn) hw
      (show -gamma a≤0 by linarith [(parameters ha).1])
    rw [Real.mul_rpow hd.le hn.le] at hpow
    exact (min_le_right _ _).trans (hpow.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hn.le _)))

/-- The actual reference solutions at the original sigma and tau spectra differ by the full all-index endpoint-sensitive three-power bound.
Use: the source profile-minus-reference-Green comparison is controlled by t times the common actual wave envelope, including every finite low-frequency mode.
Article: jacobi, Proposition C.4.
Proof: the same positive index frequency threshold lies below both genuine spectral energies. Apply the proved endpoint-sensitive real mean-value bound, the all-index McMahon displacement and the exact minimum rescaling. -/
theorem endpoint_spectral_difference {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k : ℕ,∀ t∈Icc (0:ℝ) (1/2),
      |realSolution a (jacobi.Bessel.sigma a ha k) t-realSolution a (eigenvalue a k) t|≤
        B*t*min (t^(gamma a)) ((k+1:ℝ)^(-gamma a))/(k+1:ℝ)^3 := by
  -- Both spectra and every finite prefix entry remain the original source objects.
  obtain ⟨C,hC,hbound⟩ := realSolution_endpoint_lipschitz ha
  obtain ⟨M,hM,herror⟩ := spectrum_error ha
  obtain ⟨d,hd,hscale⟩ := spectral_frequency_lower ha
  let D := max 1 (d^(-gamma a))
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C*D*M/d,by positivity,fun k t ht => ?_⟩
  have hn : 0<(k+1:ℝ) := by positivity
  have hdp : 0<d*(k+1:ℝ) := mul_pos hd hn
  have hB := (sq_le_sq₀ hdp.le (besselFrequency_pos ha k).le).mpr (hscale k).1
  have hP := (sq_le_sq₀ hdp.le (jacobi.Bessel.phaseGrid_pos ha k).le).mpr (hscale k).2
  rw [besselFrequency_sq] at hB
  rw [← reference_energy_phase] at hP
  have hh := hbound (d*(k+1:ℝ)) hdp (eigenvalue a k) (jacobi.Bessel.sigma a ha k) hP hB t ht
  have hm := spectral_minimum_bound ha hd ht.1 k (le_refl (d*(k+1:ℝ)))
  calc
    _ ≤ (C*t/(d*(k+1:ℝ))*min (t^(gamma a)) ((d*(k+1:ℝ))^(-gamma a)))*
        |jacobi.Bessel.sigma a ha k-eigenvalue a k| := hh
    _ ≤ (C*t/(d*(k+1:ℝ))*(D*min (t^(gamma a)) ((k+1:ℝ)^(-gamma a))))*
        (M/(k+1:ℝ)^2) := mul_le_mul
      (mul_le_mul_of_nonneg_left hm (div_nonneg (mul_nonneg hC.le ht.1) hdp.le))
      (herror k) (abs_nonneg _) (mul_nonneg
        (div_nonneg (mul_nonneg hC.le ht.1) hdp.le)
        (mul_nonneg hD.le (le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg hn.le _))))
    _ = _ := by field_simp [hd.ne',hn.ne']

end
end jacobi.Reference
