import jacobi.Reference.RealSpectralDerivatives
import jacobi.Reference.SpectralSolutions

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
At the two actual original spectra, the reference solution difference
is O(k^(-gamma-3)) and its genuine spatial slope difference is
O(k^(-gamma-2)). These bounds use the sharp actual energy derivatives
and the already proved original McMahon displacement, and apply
uniformly on the whole required physical domains.
Use: in the spatial derivative of f_sigma tensor f_sigma minus f_tau tensor f_tau, multiplication by the true O(k^(1-gamma)) slope remains O(k^(-2-2*gamma)).
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual reference solutions at the two genuine spectra differ by the full extra three inverse powers of the index.
Use: in the spatial derivative of f_sigma tensor f_sigma minus f_tau tensor f_tau, multiplication by the true O(k^(1-gamma)) slope remains O(k^(-2-2*gamma)).
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the proved original spectral scale supplies a common frequency
threshold along the entire actual energy segment. Apply the sharp
real energy mean-value inequality and the genuine O(k^-2) McMahon displacement. -/
theorem spectral_solution_difference_sharp {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ k:ℕ in atTop,∀ t∈Icc (0:ℝ) (1/2),
      |realSolution a (jacobi.Bessel.sigma a ha k) t-realSolution a (eigenvalue a k) t|≤
        B*(k+1:ℝ)^(-gamma a)/(k+1:ℝ)^3 := by
  -- Every source estimate concerns the same original reference function at the same original enumerated spectral points.
  obtain ⟨C,hC,hbound⟩ := realSolution_energy_lipschitz_sharp ha
  obtain ⟨M,hM,herror⟩ := spectrum_error ha
  obtain ⟨d,hd,hscale⟩ := spectral_energy_scale ha
  refine ⟨C*d^(-gamma a)*M/d,by positivity,?_⟩
  filter_upwards [hscale] with k hk t ht
  have hkp : 0<(k+1:ℝ) := by positivity
  have hh := hbound (d*(k+1:ℝ)) hk.1 (eigenvalue a k) (jacobi.Bessel.sigma a ha k)
    (by linarith [hk.2.1]) (by linarith [hk.2.2]) t ht
  apply hh.trans
  calc
    _ ≤ (C*(d*(k+1:ℝ))^(-gamma a)/(d*(k+1:ℝ)))*(M/(k+1:ℝ)^2) :=
      mul_le_mul_of_nonneg_left (herror k) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hd.le hkp.le]
      field_simp [hd.ne',hkp.ne']

/-- The actual spatial reference slopes at the two genuine spectra have the full extra two inverse powers of the index, uniformly away from zero.
Use: together with spectral_solution_difference_sharp, gives the original tensor-derivative difference estimate in Appendix C.2 (c), needed for continuous termwise differentiation of the regularized kernel.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: beyond a genuine finite index the actual common spectral
frequency exceeds the proved strip derivative threshold. Its sharp
real mean-value bound multiplied by the original McMahon error gives the printed power. -/
theorem spectral_slope_difference_sharp {a : ℝ} (ha : -1<a) {d0 : ℝ} (hd0 : 0<d0) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ k:ℕ in atTop,∀ t∈Icc d0 (1/2),
      |realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t|≤
        B*(k+1:ℝ)^(-gamma a)/(k+1:ℝ)^2 := by
  -- The threshold is derived from the actual original spectral scale, rather than required as a new premise.
  obtain ⟨C,hC,hbound⟩ := realSlope_energy_lipschitz ha hd0
  obtain ⟨M,hM,herror⟩ := spectrum_error ha
  obtain ⟨d,hd,hscale⟩ := spectral_energy_scale ha
  obtain ⟨K,hK⟩ := exists_nat_gt ((2*max 1 (1/d0))/d)
  refine ⟨C*d^(-gamma a)*M,by positivity,?_⟩
  filter_upwards [hscale,eventually_ge_atTop K] with k hk hKk t ht
  have hkp : 0<(k+1:ℝ) := by positivity
  have hcast : (K:ℝ)≤k := by exact_mod_cast hKk
  have hthr : 2*max 1 (1/d0)≤d*(k+1:ℝ) := by
    have h := (div_lt_iff₀ hd).mp hK
    nlinarith
  have hh := hbound (d*(k+1:ℝ)) hthr (eigenvalue a k) (jacobi.Bessel.sigma a ha k)
    (by linarith [hk.2.1]) (by linarith [hk.2.2]) t ht
  apply hh.trans
  calc
    _ ≤ (C*(d*(k+1:ℝ))^(-gamma a))*(M/(k+1:ℝ)^2) :=
      mul_le_mul_of_nonneg_left (herror k) (by positivity)
    _ = _ := by rw [Real.mul_rpow hd.le hkp.le]; ring

end
end jacobi.Reference
