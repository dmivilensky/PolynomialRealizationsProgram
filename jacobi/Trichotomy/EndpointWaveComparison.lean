import jacobi.Reference.EndpointSpectralScale
import jacobi.GelfandLevitan.EndpointStripCorrection
import jacobi.GelfandLevitan.Profiles

/-!
Article: jacobi, Proposition C.4.
Use: endpoint_wave_comparison and the profile difference estimate keep the same scale before dividing by the original norming constants.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine physical endpoint and inverse-index minimum used in the source spectral wave comparison.
Use: endpoint_wave_comparison and the profile difference estimate keep the same scale before dividing by the original norming constants.
Article: jacobi, Proposition C.4.
-/
def waveEnvelope (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  min (t^(gamma a)) ((k+1:ℝ)^(-gamma a))

/-- The original transformed and reference spectral waves share one endpoint-sensitive envelope, and their true difference gains one full spatial factor.
Use: the genuine profile-minus-reference-Green series is bounded by the source's two summable endpoint envelopes, leading to its o(t) limit.
Article: jacobi, Proposition C.4.
Proof: insert the actual positive Bessel and reference frequencies into the proved strip bounds and rescale by their common all-index lower scale. Split u(sigma)-f(tau) into the actual GL correction at sigma and the original sigma/tau spectral difference, retaining the factor t in both. -/
theorem endpoint_wave_comparison (a : ℝ) (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k : ℕ,∀ t : HalfInterval,
      |realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t|≤C*waveEnvelope a k t ∧
      |eigenfunction a k t|≤C*waveEnvelope a k t ∧
      |realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t-eigenfunction a k t|≤
        C*(t:ℝ)*waveEnvelope a k t := by
  -- All bounds concern the same actual enumerated spectral waves, including the finite low-frequency prefix.
  obtain ⟨A,hA,hf⟩ := wave_strip_bound ha 0
  obtain ⟨B,hB,hu⟩ := transformedSolution_strip_bound a ha 0
  obtain ⟨D,hD,hcorr⟩ := transformedSolution_strip_correction a ha 0
  obtain ⟨P,hP,hdiff⟩ := endpoint_spectral_difference ha
  obtain ⟨d,hd,hscale⟩ := spectral_frequency_lower ha
  let H := max 1 (d^(-gamma a))
  have hH : 0<H := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C := A*H+B*H+D*H+P
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun k t => ?_⟩
  have hm : 0≤waveEnvelope a k t := le_min (Real.rpow_nonneg t.property.1 _)
    (Real.rpow_nonneg (by positivity) _)
  have hsig : (jacobi.Jacobi.endpointCorrection a:ℂ)+(besselFrequency a ha k:ℂ)^2=
      (jacobi.Bessel.sigma a ha k:ℂ) := by
    rw [← Complex.ofReal_pow,besselFrequency_sq]
    push_cast
    ring
  have htau : (jacobi.Bessel.phaseGrid a k:ℂ)^2=
      (eigenvalue a k:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ) := by
    exact_mod_cast (reference_energy_phase a k).symm
  have hmB : min ((t:ℝ)^(gamma a)) ((besselFrequency a ha k)^(-gamma a))≤H*waveEnvelope a k t :=
    spectral_minimum_bound ha hd t.property.1 k (hscale k).1
  have hmP : min ((t:ℝ)^(gamma a)) ((jacobi.Bessel.phaseGrid a k)^(-gamma a))≤H*waveEnvelope a k t :=
    spectral_minimum_bound ha hd t.property.1 k (hscale k).2
  have hnormB : ‖(besselFrequency a ha k:ℂ)‖=besselFrequency a ha k := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (besselFrequency_pos ha k)]
  have hnormP : ‖(jacobi.Bessel.phaseGrid a k:ℂ)‖= jacobi.Bessel.phaseGrid a k := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (jacobi.Bessel.phaseGrid_pos ha k)]
  have hu0 := hu (besselFrequency a ha k:ℂ)
    (Complex.ofReal_ne_zero.mpr (besselFrequency_pos ha k).ne') (by simp) t
  rw [hsig,hnormB] at hu0
  have hu1 : |realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t|≤(B*H)*waveEnvelope a k t := by
    exact ((Complex.abs_re_le_norm _).trans hu0).trans
      ((mul_le_mul_of_nonneg_left hmB hB.le).trans_eq (by ring))
  have hf0 := hf (jacobi.Bessel.phaseGrid a k:ℂ)
    (Complex.ofReal_ne_zero.mpr (jacobi.Bessel.phaseGrid_pos ha k).ne') (by simp) t t.property
  rw [← solution_eq_wave a htau,hnormP] at hf0
  have hf1 : |eigenfunction a k t|≤(A*H)*waveEnvelope a k t := by
    rw [← realSolution_at_reference]
    exact ((Complex.abs_re_le_norm _).trans hf0).trans
      ((mul_le_mul_of_nonneg_left hmP hA.le).trans_eq (by ring))
  have hc0 := hcorr (besselFrequency a ha k:ℂ)
    (Complex.ofReal_ne_zero.mpr (besselFrequency_pos ha k).ne') (by simp) t
  rw [hsig,hnormB] at hc0
  have hc1 : |realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t-
      realSolution a (jacobi.Bessel.sigma a ha k) t|≤(D*H)*(t:ℝ)*waveEnvelope a k t := by
    have h := (Complex.abs_re_le_norm _).trans hc0
    simp only [Complex.sub_re] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hmB (mul_nonneg hD.le t.property.1)).trans_eq (by ring))
  have hp1 : |realSolution a (jacobi.Bessel.sigma a ha k) t-eigenfunction a k t|≤
      P*(t:ℝ)*waveEnvelope a k t := by
    rw [← realSolution_at_reference]
    exact (hdiff k t t.property).trans (div_le_self (mul_nonneg (mul_nonneg hP.le t.property.1) hm)
      (one_le_pow₀ (show (1:ℝ)≤k+1 by linarith [Nat.cast_nonneg (α := ℝ) k])))
  refine ⟨hu1.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; nlinarith [mul_pos hA hH,mul_pos hB hH,mul_pos hD hH]) hm),
    hf1.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; nlinarith [mul_pos hA hH,mul_pos hB hH,mul_pos hD hH]) hm),?_⟩
  have habs := abs_sub_le (realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t)
    (realSolution a (jacobi.Bessel.sigma a ha k) t) (eigenfunction a k t)
  have hsmall : D*H+P≤C := by dsimp only [C]; nlinarith [mul_pos hA hH,mul_pos hB hH]
  calc
    _ ≤ (D*H)*(t:ℝ)*waveEnvelope a k t+P*(t:ℝ)*waveEnvelope a k t :=
      habs.trans (add_le_add hc1 hp1)
    _ = (D*H+P)*((t:ℝ)*waveEnvelope a k t) := by ring
    _ ≤ C*((t:ℝ)*waveEnvelope a k t) :=
      mul_le_mul_of_nonneg_right hsmall (mul_nonneg t.property.1 hm)
    _ = C*(t:ℝ)*waveEnvelope a k t := by ring

end
end jacobi.Trichotomy
