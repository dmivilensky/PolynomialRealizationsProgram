import nesterov.IQC.KYP.Potential

/-! The source potential uses only the M value coordinates prescribed by the certificate. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
variable {a : Spectral.SymbolPair} {t : ℝ}

theorem potentialCoefficient_zero_of_horizon_le (cert : Duality.StrictCertificate a t)
    {j : ℕ} (hj : potentialHorizon cert≤j) : potentialCoefficient cert j=0 := by
  unfold potentialCoefficient
  have hs : (∑ n∈cert.lags,if j<n then 2*Real.exp (n*t)*(cert.α n-cert.β n) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnM : n≤potentialHorizon cert:=Finset.le_sup (f:=id) hn
    simp only [ite_eq_right (not_lt.mpr (hnM.trans hj))]
  rw [hs,mul_zero]

/-- The value correction has fixed scalar coefficients on exactly the
allowed M consecutive potential evaluations. -/
theorem sourcePotential_eq_coefficients_of_bound (cert : Duality.StrictCertificate a t)
    {M : ℕ} (hM : ∀ n∈cert.lags,n≤M) (h : ℕ→ℝ) (k : ℕ) :
    sourcePotential cert h k=∑ j∈Finset.range M,potentialCoefficient cert j*h (k+j) := by
  have hH : potentialHorizon cert≤M:=Finset.sup_le hM
  rw [sourcePotential_eq_coefficients]
  apply Finset.sum_subset (Finset.range_mono hH)
  intro j _ hj
  have hjH : potentialHorizon cert≤j:=by simpa only [Finset.mem_range,not_lt] using hj
  rw [potentialCoefficient_zero_of_horizon_le cert hjH,zero_mul]

end
end nesterov.IQC.KYP
