import chebyshev1.Realization.OperatorL2
import chebyshev1.Realization.UniversalGain
import chebyshev1.Jacobi.EndpointProfile
import chebyshev1.Jacobi.PrefixBounds
import chebyshev1.SineJacobi.FiniteBounds

/-! Exact gain constants for time-l2 operator perturbations of endpoint-maximal
Jacobi methods, and compatibility of their Green profile with the signed one. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial
open scoped BigOperators
variable (J : JacobiData) (I : SpectralInterval)

theorem signedEndpointProfile_eq {N : ℕ} (h : J.Admissible I N)
    {c : ℝ} (hc : c ≠ 0) (ht : J.leading N = C c*Polynomial.Chebyshev.T ℝ N)
    (s : ℕ) (hs : s < N) :
    (J.realization I).signedEndpointProfile I N s = J.endpointProfile N s := by
  rw [Realization.signedEndpointProfile,J.kernel_endpoint_profile I h hc ht s hs]
  have he : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
  field_simp [he,I.delta_pos.ne']

theorem opNorm_linearResponse_le_gain_l2 {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (ha : J.Admissible I N) (hm : J.EndpointMax N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ) :
    opNorm ((J.realization I).linearResponse N H E) ≤
      (J.realization I).gain I N*Real.sqrt (∑ s ∈ Finset.range N, (opNorm (E s))^2) := by
  apply (J.realization I).opNorm_linearResponse_le_gain_l2_of_kernel_factorization I N
    (fun _ => -(2/(I.delta*J.den I N)))
    (fun s => J.spectralBlock I (s+1) (N-(s+1))) (fun s => J.spectralBlock I 0 s)
    (by
      intro s hs lam _ nu _
      simpa only [J.spectralBlock_eval,JacobiData.leading] using J.kernel_eq I ha s hs lam nu)
    I.mu I.mu ⟨le_rfl,I.mu_lt_L.le⟩ ⟨le_rfl,I.mu_lt_L.le⟩
    (by
      intro s hs lam hlam
      rw [J.spectralBlock_eval,J.spectralBlock_eval,I.z_mu]
      exact (hm (s+1) (N-(s+1)) (by omega) _ (I.z_mem hlam)).trans (le_abs_self _))
    (by
      intro s hs nu hnu
      rw [J.spectralBlock_eval,J.spectralBlock_eval,I.z_mu]
      exact (hm 0 s (by omega) _ (I.z_mem hnu)).trans (le_abs_self _))
    H hH hspec E

end
end chebyshev1.JacobiData

namespace chebyshev1.Prefix
noncomputable section
open scoped BigOperators
theorem opNorm_linearResponse_le_gain_l2 {d : Type*} [Fintype d] [DecidableEq d]
    (I : SpectralInterval) (N : ℕ) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ) :
    opNorm ((realization I).linearResponse N H E) ≤
      (realization I).gain I N*Real.sqrt (∑ s ∈ Finset.range N, (opNorm (E s))^2) := by
  simpa only [jacobi_realization] using jacobiData.opNorm_linearResponse_le_gain_l2 I
    (jacobi_admissible I N) (jacobi_endpointMax N) H hH hspec E
end
end chebyshev1.Prefix

namespace chebyshev1.SineJacobi
noncomputable section
open scoped BigOperators
theorem opNorm_linearResponse_le_gain_l2 {d : Type*} [Fintype d] [DecidableEq d]
    (I : SpectralInterval) {N : ℕ} (hN : 0 < N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ) :
    opNorm (((data N).realization I).linearResponse N H E) ≤
      ((data N).realization I).gain I N*Real.sqrt (∑ s ∈ Finset.range N, (opNorm (E s))^2) :=
  (data N).opNorm_linearResponse_le_gain_l2 I (admissible I N hN) (endpointMax N hN)
    H hH hspec E
end
end chebyshev1.SineJacobi
