import chebyshev1.Jacobi.RatioAlgorithm
import chebyshev1.SineJacobi.Algorithm

/-! The sine-chain algorithm in scalar ratio coordinates. -/
namespace chebyshev1.SineJacobi
noncomputable section
variable (I : SpectralInterval)

theorem ratio_initial (N : ℕ) :
    (data N).ratioState I 1 = 1 / I.eta ∧
      (data N).ratioDenominator I 0 = I.eta := by
  simp [JacobiData.ratioState, JacobiData.ratioDenominator]

/-- The bounded scalar state, its positive divisor, and all advertised coefficients. -/
theorem ratio_coefficients (N : ℕ) (hN : 0 < N) (s : ℕ) (hs : 0 < s) (hsN : s < N) :
    let u := (data N).ratioState I s
    let d := I.eta - couplingSq N s * u
    0 < u ∧ 0 < d ∧
      u = (data N).den I (s - 1) / (data N).den I s ∧
      ((data N).method I).a s = I.eta / d ∧
      ((data N).method I).b s = -(couplingSq N s * u / d) ∧
      ((data N).method I).gamma s = 2 / (I.delta * d) ∧
      (data N).ratioState I (s + 1) = 1 / d := by
  dsimp only
  have h := admissible I N hN
  have hd : (data N).ratioDenominator I s =
      I.eta - couplingSq N s * (data N).ratioState I s := by
    simp [JacobiData.ratioDenominator, data_aSq N s hs hsN]
  have hu := (data N).ratioState_eq_den_ratio I h (s - 1) (by omega)
  rw [show s - 1 + 1 = s by omega] at hu
  refine ⟨?_, ?_, hu, ?_, ?_, ?_, ?_⟩
  · simpa [show s - 1 + 1 = s by omega] using
      (data N).ratioState_pos I h (s - 1) (by omega)
  · simpa [hd] using (data N).ratioDenominator_pos I h s (by omega)
  · rw [← (data N).ratioMethod_a I h s (by omega)]
    simp [JacobiData.ratioMethod, hd]
  · have hb := (data N).ratioMethod_b I h (s - 1) (by omega)
    rw [show s - 1 + 1 = s by omega] at hb
    rw [← hb]
    simp [JacobiData.ratioMethod, hd, data_aSq N s hs hsN]
  · rw [← (data N).ratioMethod_gamma I h s (by omega)]
    simp [JacobiData.ratioMethod, hd]
  · rw [JacobiData.ratioState_succ, hd]

/-- The ratio execution has exactly the same terminal output, also when `N = 1`. -/
theorem ratio_quadraticError_exact {d : Type*} [Fintype d] [DecidableEq d]
    (N : ℕ) (hN : 0 < N) (H : Matrix d d ℝ) (e0 : d → ℝ) :
    ((data N).ratioMethod I).quadraticError H e0 N =
      (Polynomial.aeval H (I.residual N)).mulVec e0 := by
  rw [(data N).ratioMethod_quadraticError I (admissible I N hN) H e0 N le_rfl]
  exact quadraticError_exact I N hN H e0

/-- The supplementary algorithm also implements the method on nonlinear objectives. -/
theorem ratio_nonlinearError {d : Type*}
    (N : ℕ) (hN : 0 < N) (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ)
    (n : ℕ) (hn : n ≤ N) :
    ((data N).ratioMethod I).nonlinearError g e0 n =
      ((data N).method I).nonlinearError g e0 n :=
  (data N).ratioMethod_nonlinearError I (admissible I N hN) g e0 n hn

end
end chebyshev1.SineJacobi
