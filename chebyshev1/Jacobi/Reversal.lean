import chebyshev1.Jacobi.InverseUniqueness
import chebyshev1.Jacobi.EndpointProfile
import chebyshev1.Jacobi.TerminalSpectrum

/-! Reversing a finite Jacobi chain reverses insertion time and exchanges the two modes. -/
namespace chebyshev1.JacobiData
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
variable (J : JacobiData) (I : SpectralInterval)

theorem reversed_leading_terminal (hsq : ∀ t, 0 ≤ J.aSq t) (N : ℕ) :
    (J.reversed N).leading N = J.leading N := by
  simpa [leading] using J.reversed_block hsq N 0 N (by omega)

theorem reversed_den_terminal (hsq : ∀ t, 0 ≤ J.aSq t) (N : ℕ) :
    (J.reversed N).den I N = J.den I N := by
  rw [den, den, J.reversed_leading_terminal hsq N]

theorem endpointProfile_reversed (hsq : ∀ t, 0 ≤ J.aSq t)
    (N s : ℕ) (hs : s < N) :
    (J.reversed N).endpointProfile N s = J.endpointProfile N (N - 1 - s) := by
  unfold endpointProfile
  rw [J.reversed_leading_terminal hsq N]
  change ((J.reversed N).block 0 s).eval 1 * _ / _ = _
  rw [J.reversed_block hsq N 0 s (by omega),
    J.reversed_block hsq N (s + 1) (N - (s + 1)) (by omega)]
  simp only [Nat.sub_zero]
  rw [show N - (s + 1) - (N - (s + 1)) = 0 by omega,
    show N - (s + 1) = N - 1 - s by omega]
  unfold leading
  rw [show N - 1 - s + 1 = N - s by omega,
    show N - (N - s) = s by omega]
  ring

theorem endpointEnergy_reversed (hsq : ∀ t, 0 ≤ J.aSq t) (N : ℕ) :
    (J.reversed N).endpointEnergy N = J.endpointEnergy N := by
  unfold endpointEnergy
  calc
    _ = ∑ s ∈ Finset.range N, (J.endpointProfile N (N - 1 - s)) ^ 2 := by
      exact Finset.sum_congr rfl (fun s hs =>
        congrArg (fun x : ℝ => x ^ 2)
          (J.endpointProfile_reversed hsq N s (Finset.mem_range.mp hs)))
    _ = _ := Finset.sum_range_reflect (fun s => (J.endpointProfile N s) ^ 2) N

theorem kernel_reversed {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    (h : J.Admissible I N) (hrev : (J.reversed N).Admissible I N)
    (s : ℕ) (hs : s < N) (lam nu : ℝ) :
    ((J.reversed N).realization I).kernel N s lam nu =
      (J.realization I).kernel N (N - 1 - s) nu lam := by
  rw [(J.reversed N).kernel_eq I hrev s hs,
    J.kernel_eq I h (N - 1 - s) (by omega), J.reversed_den_terminal I hsq N]
  unfold leading
  rw [J.reversed_block hsq N (s + 1) (N - (s + 1)) (by omega),
    J.reversed_block hsq N 0 s (by omega)]
  simp only [Nat.sub_zero]
  rw [show N - (s + 1) - (N - (s + 1)) = 0 by omega,
    show N - (s + 1) = N - 1 - s by omega,
    show N - 1 - s + 1 = N - s by omega,
    show N - (N - s) = s by omega]
  ring

theorem kernelNorm_reversed {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    (h : J.Admissible I N) (hrev : (J.reversed N).Admissible I N) (lam nu : ℝ) :
    ((J.reversed N).realization I).kernelNorm N lam nu =
      (J.realization I).kernelNorm N nu lam := by
  unfold Realization.kernelNorm
  congr 1
  calc
    _ = ∑ s ∈ Finset.range N,
        ((J.realization I).kernel N (N - 1 - s) nu lam) ^ 2 := by
      exact Finset.sum_congr rfl (fun s hs =>
        congrArg (fun x : ℝ => x ^ 2)
          (J.kernel_reversed I hsq h hrev s (Finset.mem_range.mp hs) lam nu))
    _ = _ := Finset.sum_range_reflect
      (fun s => ((J.realization I).kernel N s nu lam) ^ 2) N

theorem gain_reversed {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    (h : J.Admissible I N) (hrev : (J.reversed N).Admissible I N) :
    ((J.reversed N).realization I).gain I N = (J.realization I).gain I N := by
  unfold Realization.gain
  congr 1
  ext v
  constructor
  · rintro ⟨lam, hl, nu, hn, rfl⟩
    exact ⟨nu, hn, lam, hl, J.kernelNorm_reversed I hsq h hrev lam nu⟩
  · rintro ⟨lam, hl, nu, hn, rfl⟩
    exact ⟨nu, hn, lam, hl, (J.kernelNorm_reversed I hsq h hrev nu lam).symm⟩

theorem reversed_admissible_of_terminal {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    {c : ℝ} (hc : c ≠ 0)
    (ht : J.leading N = Polynomial.C c * Polynomial.Chebyshev.T ℝ N) :
    (J.reversed N).Admissible I N :=
  (J.reversed N).admissible_of_terminal I (J.reversed_aSq_nonneg hsq N) hc
    ((J.reversed_leading_terminal hsq N).trans ht)

/-- Terminal exactness alone supplies admissibility of both chains. -/
theorem gain_reversed_of_terminal {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    {c : ℝ} (hc : c ≠ 0)
    (ht : J.leading N = Polynomial.C c * Polynomial.Chebyshev.T ℝ N) :
    ((J.reversed N).realization I).gain I N = (J.realization I).gain I N :=
  J.gain_reversed I hsq (J.admissible_of_terminal I hsq hc ht)
    (J.reversed_admissible_of_terminal I hsq hc ht)

end
end chebyshev1.JacobiData
