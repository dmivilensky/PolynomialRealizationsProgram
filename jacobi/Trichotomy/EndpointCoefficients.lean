import jacobi.Reference.EnergyGreenEndpoint
import jacobi.Reference.NormingBounds
import jacobi.Reference.NormBounds
import jacobi.Bessel.ZeroGeometry

/-!
Article: jacobi, Proposition C.4.
The actual Bessel and reference reciprocal spectra have uniform
inverse-square bounds when tau_1>0. Their original weighted difference
Lambda_k*rho_k-2/tau_k has an all-index inverse-fourth bound. The
source's supercritical order range itself discharges tau_1>0.
Use: the zero-energy Green lemma applies to every order in Proposition C.4's alpha>-1/2 case without an extra spectral premise.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference
set_option backward.isDefEq.respectTransparency false

/-- The original first reference eigenvalue is positive throughout the source's supercritical endpoint range.
Use: the zero-energy Green lemma applies to every order in Proposition C.4's alpha>-1/2 case without an extra spectral premise.
Article: jacobi, Proposition C.4.
Proof: substitute alpha=2*gamma-3/2 into tau_1. The resulting expression is (pi^2-4)*gamma^2+6*gamma-2, strictly positive for gamma>1/2. -/
theorem reference_first_pos_supercritical {a : ℝ} (h : -(1/2:ℝ)<a) :
    0<eigenvalue a 0 := by
  have hg : 1/2<gamma a := by dsimp only [gamma]; linarith
  have hpi : 0<Real.pi^2-4 := by nlinarith [Real.pi_gt_three]
  have hid : eigenvalue a 0=(Real.pi^2-4)*(gamma a)^2+6*gamma a-2 := by
    dsimp only [eigenvalue,gamma,jacobi.Jacobi.endpointCorrection]
    norm_num only [Nat.cast_zero,zero_add]
    ring
  rw [hid]
  nlinarith [mul_nonneg hpi.le (sq_nonneg (gamma a))]

/-- Both original squared spectral sequences have one positive all-index quadratic lower scale when the first reference eigenvalue is positive.
Use: endpoint_coefficient_bounds obtains the actual reciprocal and weight-difference bounds with every finite original mode retained.
Article: jacobi, Proposition C.4.
Proof: square the proved actual Bessel linear lower bound. For the reference spectrum use tau_k=tau_1+pi^2*k^2+2*pi^2*k*gamma and the positive minimum of tau_1 and pi^2. -/
theorem endpoint_squared_spectral_lower {a : ℝ} (ha : -1<a) (h0 : 0<eigenvalue a 0) :
    ∃ s r : ℝ,0<s ∧ 0<r ∧ ∀ k : ℕ,
      s*(k+1:ℝ)^2≤ jacobi.Bessel.sigma a ha k ∧ r*(k+1:ℝ)^2≤eigenvalue a k := by
  -- Positivity of every genuine original eigenvalue controls the finite spectral prefix as well as the quadratic tail.
  obtain ⟨c,_C,hc,_hC,hZ⟩ := jacobi.Bessel.positiveZero_linear_bounds ha
  let r := min (eigenvalue a 0) (Real.pi^2)/2
  have hr : 0<r := half_pos (lt_min h0 (sq_pos_of_pos Real.pi_pos))
  have hr0 : 2*r≤eigenvalue a 0 := by dsimp only [r]; linarith [min_le_left (eigenvalue a 0) (Real.pi^2)]
  have hrpi : 2*r≤Real.pi^2 := by dsimp only [r]; linarith [min_le_right (eigenvalue a 0) (Real.pi^2)]
  refine ⟨c^2,r,by positivity,hr,fun k => ?_⟩
  have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hs := (sq_le_sq₀ (by positivity : 0≤c*(k+1:ℝ)) (jacobi.Bessel.positiveZero_properties ha k).1.le).mpr (hZ k).1
  have hid : eigenvalue a k=eigenvalue a 0+Real.pi^2*(k:ℝ)^2+2*Real.pi^2*(k:ℝ)*gamma a := by
    dsimp only [eigenvalue]
    norm_num only [Nat.cast_zero,zero_add]
    ring
  refine ⟨by rw [← (jacobi.Bessel.positiveZero_properties ha k).2]; nlinarith [hs],?_⟩
  rw [hid]
  have hquad := mul_le_mul_of_nonneg_right hrpi (sq_nonneg (k:ℝ))
  nlinarith [mul_nonneg hr.le (sq_nonneg ((k:ℝ)-1)),
    mul_nonneg (mul_nonneg (by positivity : 0≤2*Real.pi^2) hk) hg.le]

/-- The actual original spectral coefficients have the complete uniform bounds used in the endpoint profile comparison.
Use: the true profile-minus-reference-Green summands are controlled by k^-4 times the wave square and t*k^-2 times the wave square, without conditional spectral estimates.
Article: jacobi, Proposition C.4.
Proof: the genuine spectra have proved positive quadratic lower bounds and bounded displacement; the original norming ratios differ from one by O(k^-2). Split the actual weighted difference into Lambda*(rho-1) and the exact reciprocal spectral difference. -/
theorem endpoint_coefficient_bounds {a : ℝ} (ha : -1<a) (h0 : 0<eigenvalue a 0) :
    ∃ A B D : ℝ,0<A ∧ 0<B ∧ 0<D ∧ ∀ k : ℕ,
      jacobi.Bessel.edgeValue a ha k≤A/(k+1:ℝ)^2 ∧
      2/eigenvalue a k≤B/(k+1:ℝ)^2 ∧
      |jacobi.Bessel.edgeValue a ha k*normingRatio a ha k-2/eigenvalue a k|≤D/(k+1:ℝ)^4 := by
  -- All coefficients and normalizations are the original source data used by the actual profile series.
  obtain ⟨s,r,hs,hr,hscale⟩ := endpoint_squared_spectral_lower ha h0
  obtain ⟨_c,_C,R,_hc,_hC,hR,hrho⟩ := normingRatio_bounds ha
  obtain ⟨M,hM,hdisp⟩ := spectrum_error_bounded ha
  refine ⟨2/s,2/r,(2/s)*R+2*M/(s*r),by positivity,by positivity,by positivity,fun k => ?_⟩
  have hn : 0<(k+1:ℝ) := by positivity
  have hsig := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  have htau := energy_gap_pos ha h0 k
  simp only [sub_zero] at htau
  have hL : jacobi.Bessel.edgeValue a ha k≤(2/s)/(k+1:ℝ)^2 :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (hscale k).1).trans_eq (by field_simp [hs.ne',hn.ne'])
  have hT : 2/eigenvalue a k≤(2/r)/(k+1:ℝ)^2 :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (hscale k).2).trans_eq (by field_simp [hr.ne',hn.ne'])
  refine ⟨hL,hT,?_⟩
  have hden := mul_le_mul (hscale k).1 (hscale k).2 (by positivity) hsig.le
  have hrecip : |jacobi.Bessel.edgeValue a ha k-2/eigenvalue a k|≤(2*M/(s*r))/(k+1:ℝ)^4 := by
    have hid : jacobi.Bessel.edgeValue a ha k-2/eigenvalue a k=
        -2*(jacobi.Bessel.sigma a ha k-eigenvalue a k)/
          (jacobi.Bessel.sigma a ha k*eigenvalue a k) := by
      rw [jacobi.Bessel.edgeValue]
      field_simp
      ring
    rw [hid,abs_div,abs_mul,abs_of_pos (mul_pos hsig htau)]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hdisp k) (by norm_num))
      (by positivity) hden).trans_eq (by field_simp [hs.ne',hr.ne',hn.ne'])
  have hid : jacobi.Bessel.edgeValue a ha k*normingRatio a ha k-2/eigenvalue a k=
      jacobi.Bessel.edgeValue a ha k*(normingRatio a ha k-1)+
        (jacobi.Bessel.edgeValue a ha k-2/eigenvalue a k) := by ring
  rw [hid]
  have hterm : |jacobi.Bessel.edgeValue a ha k*(normingRatio a ha k-1)|≤
      ((2/s)/(k+1:ℝ)^2)*(R/(k+1:ℝ)^2) := by
    rw [abs_mul,abs_of_pos ((jacobi.Bessel.edgeValue_properties ha).1 k)]
    exact mul_le_mul hL (hrho k).2.2 (abs_nonneg _) (by positivity)
  exact ((abs_add_le _ _).trans (add_le_add hterm hrecip)).trans_eq (by field_simp [hs.ne',hr.ne',hn.ne'])

end
end jacobi.Trichotomy
