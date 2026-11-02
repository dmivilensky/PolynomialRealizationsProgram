import jacobi.Reference.ContourLower
import jacobi.Reference.ContourProduct
import jacobi.Reference.EndpointFrequency
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Use: parity_integrand_contour_bound and parity_contour_integral_limit supply the vanishing-integral side of the parity residue identity.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual meromorphic integrand whose residues are the signed differences of the original reference and Bessel kernel summands.
Use: parity_integrand_contour_bound and parity_contour_integral_limit supply the vanishing-integral side of the parity residue identity.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def parityIntegrand (a t s : ℝ) (z : ℂ) : ℂ :=
  solution a z t*solution a z s*((characteristicSigma a z)⁻¹-(characteristicTau a z)⁻¹)

/-- The norm of the genuine parity integrand equals the original wave product times the relative characteristic error divided by the target characteristic.
Use: parity_integrand_contour_bound combines the three independently proved contour bounds without discarding the exact characteristic normalization.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the exact reciprocal difference is minus (Delta_sigma/Delta_tau-1)/Delta_sigma; both genuine characteristic nonvanishing premises are checked on the original contours. -/
theorem parityIntegrand_norm (a t s : ℝ) (z : ℂ)
    (hs : characteristicSigma a z≠0) (ht : characteristicTau a z≠0) :
    ‖parityIntegrand a t s z‖=
      (‖solution a z t*solution a z s‖*‖characteristicSigma a z/characteristicTau a z-1‖)/
        ‖characteristicSigma a z‖ := by
  have he : (characteristicSigma a z)⁻¹-(characteristicTau a z)⁻¹=
      -(characteristicSigma a z/characteristicTau a z-1)/characteristicSigma a z := by
    field_simp [hs,ht]
    ring
  rw [parityIntegrand,he,norm_mul,norm_div,norm_neg]
  ring

/-- The exact powers in the actual contour estimates leave one inverse frequency after the Gamma characteristic power is cancelled.
Use: parity_integrand_contour_bound combines the two wave powers, the relative inverse-square error, and the absolute characteristic lower bound to obtain R_m^-3.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: use the positive-base real power laws; the two exponents differ by minus one. -/
theorem parity_contour_power {R : ℝ} (hR : 0<R) (g : ℝ) :
    (R^(-g))^2/R^(1-2*g)=1/R := by
  rw [← Real.rpow_two (R^(-g)),← Real.rpow_mul hR.le,← Real.rpow_sub hR,
    show -g*2-(1-2*g)= -1 by ring,Real.rpow_neg_one,one_div]

/-- The actual parity integrand satisfies the complete uniform inverse-cubic bound on all sufficiently large original energy circles.
Use: parity_contour_integral_limit proves vanishing of the genuine contour integrals, which the residue argument identifies with the signed kernel partial sums.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the genuine wave product contributes R_m^(-2*gamma)*exp((t+s)*abs(Im omega)), the actual relative characteristic error contributes R_m^-2, and the proved absolute Delta_tau lower bound controls Delta_sigma. Since t+s<=1, the remaining exponential is at most one. -/
theorem parity_integrand_contour_bound {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∃ M : ℕ,∀ m : ℕ,M≤m → ∀ omega : ℂ,
      ‖omega‖=contourRadius a m → ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
      ‖parityIntegrand a t s ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤
        B/(contourRadius a m)^3 := by
  -- All three constants are conclusions for the actual original functions on the same original circles.
  obtain ⟨A,hA,hwave⟩ := wave_minimum_high_frequency ha
  obtain ⟨c,hc,M₁,hlower⟩ := contour_characteristicTau_lower ha
  obtain ⟨D,hD,M₂,hrelative⟩ := contour_characteristic_bound ha
  refine ⟨2*A^2*D/c,by positivity,max M₁ M₂,fun m hm omega homega t ht s hs => ?_⟩
  let R : ℝ := contourRadius a m
  let z : ℂ := (jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2
  have hR : 0<R := contourRadius_pos ha m
  have hR1 : 1≤‖omega‖ := by rw [homega]; exact (contourRadius_one_lt ha m).le
  have hsq : omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ) := by dsimp [z]; ring
  have hz : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=R^2 := by rw [← hsq,norm_pow,homega]
  obtain ⟨hSigma,herr,hcompare⟩ := hrelative m ((le_max_right _ _).trans hm) z hz
  have hτ := characteristicTau_contour_ne_zero ha m hz
  have hbase : 0<(c/2)*R^(1-2*gamma a)*Real.exp |omega.im| := by positivity
  have hSigmaLower : (c/2)*R^(1-2*gamma a)*Real.exp |omega.im|≤‖characteristicSigma a z‖ := by
    have h := hlower m ((le_max_left _ _).trans hm) omega homega
    change c*R^(1-2*gamma a)*Real.exp |omega.im|≤‖characteristicTau a z‖ at h
    linarith
  have hf (u : ℝ) (hu : u∈Icc (0:ℝ) (1/2)) :
      ‖solution a z u‖≤A*R^(-gamma a)*Real.exp (u*|omega.im|) := by
    rw [solution_eq_wave a hsq]
    have h := hwave omega hR1 u hu
    rw [homega] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hA.le) (Real.exp_pos _).le)
  have hg : ‖solution a z t*solution a z s‖≤
      A^2*(R^(-gamma a))^2*Real.exp |omega.im| := by
    rw [norm_mul]
    calc
      _ ≤ (A*R^(-gamma a)*Real.exp (t*|omega.im|))*(A*R^(-gamma a)*Real.exp (s*|omega.im|)) :=
        mul_le_mul (hf t ht) (hf s hs) (norm_nonneg _) (by positivity)
      _ = A^2*(R^(-gamma a))^2*Real.exp ((t+s)*|omega.im|) := by rw [add_mul,Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (show t+s≤1 by linarith [ht.2,hs.2]) (abs_nonneg omega.im))) (by positivity)
  rw [parityIntegrand_norm a t s z hSigma hτ]
  have hnum := mul_le_mul hg herr (norm_nonneg _) (by positivity)
  have hquot := div_le_div₀ (by positivity : 0≤(A^2*(R^(-gamma a))^2*Real.exp |omega.im|)*(D/R^2)) hnum hbase hSigmaLower
  apply hquot.trans_eq
  change ((A^2*(R^(-gamma a))^2*Real.exp |omega.im|)*(D/R^2))/
    ((c/2)*R^(1-2*gamma a)*Real.exp |omega.im|)=(2*A^2*D/c)/R^3
  calc
    _ = ((2*A^2*D/c)/R^2)*((R^(-gamma a))^2/R^(1-2*gamma a)) := by
      field_simp [hR.ne',hc.ne',Real.exp_ne_zero,Real.rpow_ne_zero hR.le hR.ne']
    _ = _ := by rw [parity_contour_power hR]; ring

end
end jacobi.Reference
