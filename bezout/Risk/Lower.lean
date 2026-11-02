import bezout.Risk.Bounds
import bezout.Lower.EndpointGain
import bezout.Probability.Signs

/-!
Article: bezout, Theorem 3.1, unrestricted additive lower bounds.
Use: actual scalar executions attain the endpoint response norm; a genuine
finite product martingale attains the stochastic endpoint energy.
Proof: the common-response Bezout identity and finite Cauchy--Schwarz.
-/

namespace bezout.Risk
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {N : ℕ}

/-- The prescribed additive endpoint scale is nonnegative. -/
theorem additiveScale_nonneg (I : chebyshev1.SpectralInterval) (N : ℕ) :
    0 ≤ Lower.additiveScale I N := by
  have hd : 1 ≤ I.den N := Polynomial.Chebyshev.one_le_eval_T_real N I.eta_gt_one.le
  have he : I.epsilon N ≤ 1 := (div_le_one (I.den_pos N)).mpr hd
  exact div_nonneg (sub_nonneg.mpr he) I.mu_pos.le

/-- Every competing exact history has at least the optimal endpoint response energy. -/
theorem additive_endpoint_energy (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) :
    Lower.additiveScale I N ^ 2 / (N : ℝ) ≤ ∑ s, (h.response s).eval I.mu ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ => (1 : ℝ)) (fun s => (h.response s).eval I.mu)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  rw [Lower.response_sum_mu h I he, neg_sq] at hc
  exact (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr (by nlinarith)

/-- The endpoint norm lower bound is the exact additive coefficient. -/
theorem additive_endpoint_norm (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) :
    Lower.additiveScale I N / Real.sqrt N ≤
      Analysis.energyNorm (fun s => (h.response s).eval I.mu) := by
  apply (sq_le_sq₀ (div_nonneg (additiveScale_nonneg I N) (Real.sqrt_nonneg _))
    (Analysis.energyNorm_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N), Analysis.energyNorm_sq]
  exact additive_endpoint_energy h I he hN

/-- An actual scalar noisy run is the terminal value plus its scalar physical responses. -/
theorem scalar_output (h : bezout.History N) (lam r : ℝ) (w : Fin N → ℝ) :
    (h.run (bezout.History.scalarOperator lam) r w).output =
      h.terminal.eval lam * r + ∑ s, (h.response s).eval lam * w s := by
  rw [h.physical_response]
  simp only [bezout.History.scalarOperator_polynomial_action]

/-- Aligning a shared error budget with the physical endpoint profile attains
its temporal norm in the actual oracle execution, including zero profiles. -/
theorem scalar_additive_attainment (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    ∃ w : Fin N → ℝ, (∑ s, ‖w s‖ ^ 2 ≤ t ^ 2) ∧
      ‖(h.run (bezout.History.scalarOperator I.mu) r w).output‖ =
        I.epsilon N * r + t * Analysis.energyNorm (fun s => (h.response s).eval I.mu) := by
  let a : Fin N → ℝ := fun s => (h.response s).eval I.mu
  let e := Analysis.energyNorm a
  have he0 : 0 ≤ e := Analysis.energyNorm_nonneg a
  have hes : e ^ 2 = ∑ s, a s ^ 2 := Analysis.energyNorm_sq a
  have hp : h.terminal.eval I.mu = I.epsilon N := by rw [he, I.residual_eval_mu]
  by_cases hz : e = 0
  · refine ⟨fun _ => 0, by simpa using sq_nonneg t, ?_⟩
    rw [scalar_output, hp]
    change ‖I.epsilon N * r + ∑ s, a s * 0‖ = I.epsilon N * r + t * e
    simp only [mul_zero, Finset.sum_const_zero, add_zero, hz, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (one_div_pos.mpr (I.den_pos N)).le hr)
  · let w : Fin N → ℝ := fun s => t / e * a s
    have hw : ∑ s, ‖w s‖ ^ 2 = t ^ 2 := by
      simp only [w, Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum, ← hes]
      field_simp
    refine ⟨w, hw.le, ?_⟩
    rw [scalar_output, hp]
    have hs : ∑ s, (h.response s).eval I.mu * w s = t * e := by
      change (∑ s, a s * (t / e * a s)) = _
      simp_rw [show ∀ s, a s * (t / e * a s) = (t / e) * a s ^ 2 by intro s; ring]
      rw [← Finset.mul_sum, ← hes]
      field_simp
    rw [hs, Real.norm_eq_abs]
    exact abs_of_nonneg (add_nonneg
      (mul_nonneg (one_div_pos.mpr (I.den_pos N)).le hr) (mul_nonneg ht he0))

/-- The fair-sign martingale attains the exact scalar endpoint MSE. -/
theorem scalar_mse_attainment (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (r σ : ℝ) :
    (∫ ω, ‖h.stochasticOutput (bezout.History.scalarOperator I.mu) r
      (bezout.Probability.Signs.stream N σ) ω‖ ^ 2 ∂bezout.Probability.Signs.law N) =
      I.epsilon N ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, (h.response s).eval I.mu ^ 2 := by
  rw [h.integral_stochasticOutput_norm_sq _ _ (bezout.Probability.Signs.martingale N σ),
    bezout.History.scalarOperator_polynomial_action, he, I.residual_eval_mu]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [bezout.History.responseOperator_apply,
    bezout.History.scalarOperator_polynomial_action, mul_pow]
  have hn (ω : Fin N → Bool) :
      (bezout.Probability.Signs.stream N σ s.val ω) ^ 2 = σ ^ 2 := by
    simpa only [bezout.Probability.Signs.stream, s.isLt, dite_true, Real.norm_eq_abs,
      sq_abs] using bezout.Probability.Signs.error_norm_sq σ s ω
  simp_rw [hn]
  simp [integral_const, mul_comm]

end
end bezout.Risk
