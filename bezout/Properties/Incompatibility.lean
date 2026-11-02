import bezout.Flat.Optima
import bezout.Gains.Spectral
import bezout.Gains.Comparison

/-!
Article: bezout, Section 4 and Appendix C, incompatibility of the exact optima.
Use: at every even horizon with positive oracle variance, an unrestricted
history cannot attain both the additive MSE and spectral linear minima.
Proof: equality in the endpoint energy inequalities forces constant temporal
profiles. The first query is fixed, whereas the two endpoint scales differ
strictly. A finite positive Chebyshev expansion proves the strict inequality.
-/

namespace bezout.Properties
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

/-- Exterior second-kind values dominate their endpoint values, strictly
at every positive degree. -/
theorem exterior_U_lower (I : chebyshev1.SpectralInterval) (s : ℕ) :
    (s : ℝ) + 1 ≤ Flat.u I s ∧ (0 < s → (s : ℝ) + 1 < Flat.u I s) := by
  have hm := (Flat.u_ratio_strictMono I).monotone (Nat.zero_le s)
  simp only [Nat.cast_zero, zero_add, Flat.u_zero, div_one] at hm
  constructor
  · simpa only [one_mul] using
      (le_div_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) + 1)).mp hm
  · intro hs
    have ht := Flat.u_ratio_strictMono I hs
    simp only [Nat.cast_zero, zero_add, Flat.u_zero, div_one] at ht
    simpa only [one_mul] using
      (lt_div_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) + 1)).mp ht

/-- The total positive source mass strictly exceeds its value at eta=1. -/
theorem flat_mass_strict (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ^ 2 / 2 < Flat.totalMass I N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hn : 0 < n := by omega
  have hs : ∀ m : ℕ, (∑ k ∈ Finset.range m, ((k : ℝ) + 1)) =
      (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have ht := Finset.sum_le_sum (s := Finset.range n)
    (fun k _ => (exterior_U_lower I k).1)
  rw [hs n] at ht
  rw [Flat.totalMass_succ]
  push_cast
  have hstrict := (exterior_U_lower I n).2 hn
  nlinarith

/-- The additive and linear endpoint scales differ strictly at every horizon N>=2. -/
theorem derivativeScale_lt_additiveScale (I : chebyshev1.SpectralInterval)
    {N : ℕ} (hN : 2 ≤ N) : Lower.derivativeScale I N < Lower.additiveScale I N := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : 0 < 4 * I.epsilon N / I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  have hs := Flat.physical_unitMass I N (by omega)
  have hs' : (4 * I.epsilon N / I.delta * Flat.totalMass I N) / N =
      Lower.additiveScale I N / N := by simpa only [Flat.unitMass, mul_div_assoc] using hs
  have hscale := (div_left_inj' hn).mp hs'
  calc
    _ = (4 * I.epsilon N / I.delta) * ((N : ℝ) ^ 2 / 2) := by
      unfold Lower.derivativeScale
      ring
    _ < (4 * I.epsilon N / I.delta) * Flat.totalMass I N :=
      mul_lt_mul_of_pos_left (flat_mass_strict I hN) hc
    _ = _ := hscale

/-- Equality in the temporal endpoint energy forces the unique constant profile. -/
theorem uniform_profile_of_energy_le {N : ℕ} (hN : 0 < N) (a : Fin N → ℝ) (S : ℝ)
    (hs : ∑ s, a s = -S) (he : ∑ s, a s ^ 2 ≤ S ^ 2 / N) (s : Fin N) :
    a s = -S / N := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hid : (∑ j, (a j + S / N) ^ 2) = (∑ j, a j ^ 2) - S ^ 2 / N := by
    have hterm (j : Fin N) : (a j + S / N) ^ 2 = a j ^ 2 + (2 * S / N) * a j + (S / N) ^ 2 := by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hz : (∑ j, (a j + S / N) ^ 2) ≤ 0 := by rw [hid]; linarith
  have hi : (a s + S / N) ^ 2 ≤ ∑ j, (a j + S / N) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin N => (a j + S / N) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ s)
  have hzero : a s + S / N = 0 := by nlinarith [sq_nonneg (a s + S / N)]
  rw [neg_div]
  linarith

/-- The actual fair-sign scalar risk is included in the universal worst-case MSE. -/
theorem scalar_mse_le_risk {N : ℕ} (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (r σ : ℝ) (hr : 0 ≤ r) :
    I.epsilon N ^ 2 * r ^ 2 + σ ^ 2 * (∑ s, (h.response s).eval I.mu ^ 2) ≤
      Risk.mseRisk h I r σ := by
  apply le_csInf (Risk.mseBounds_nonempty h I he r σ hr)
  intro C hb
  have hu := hb ℝ (Fin N → Bool) (Probability.Signs.law N) (Probability.Signs.past N σ)
    (Probability.Signs.stream N σ) (Probability.Signs.martingale N σ)
    (fun s hs => by rw [Probability.Signs.conditional_variance N σ s hs])
    (bezout.History.scalarOperator I.mu)
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) r
    (by simp [abs_of_nonneg hr])
  simpa only [Risk.scalar_mse_attainment h I he r σ] using hu

/-- Positive-variance additive MSE optimality forces every physical endpoint response. -/
theorem mse_optimal_responses {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hopt : Risk.mseRisk h I r σ = Risk.mseOptimum I N r σ) (s : Fin N) :
    (h.response s).eval I.mu = -Lower.additiveScale I N / N := by
  have hu := scalar_mse_le_risk h I he r σ hr
  rw [hopt] at hu
  unfold Risk.mseOptimum at hu
  have he' : (∑ j, (h.response j).eval I.mu ^ 2) ≤ Lower.additiveScale I N ^ 2 / N := by
    rw [mul_div_assoc] at hu
    nlinarith [sq_pos_of_pos hσ]
  exact uniform_profile_of_energy_le hN _ _ (Lower.response_sum_mu h I he) he' s

/-- At even horizons spectral linear optimality forces every endpoint kernel product. -/
theorem even_linear_optimal_products {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (heven : Even N) (hopt : h.spectralGain I = Lower.linearGain I N) (s : Fin N) :
    Lower.physicalKernel h s I.mu I.mu = -Lower.derivativeScale I N / N := by
  have hb := h.physical_kernelNorm_le_gain I (x := I.mu) (y := I.mu)
    ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩
  rw [hopt] at hb
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (Lower.linearGain_nonneg I N)).mpr hb
  rw [Real.sq_sqrt (Lower.physicalKernelSq_nonneg _ _ _), Lower.linearGain_sq I hN] at hs
  have hodd : ¬Odd N := Nat.not_odd_iff_even.mpr heven
  simp only [Lower.linearCorrectionSq, hodd, ite_false, mul_one] at hs
  exact uniform_profile_of_energy_le (by omega) _ _ (Lower.kernel_sum_mu h I he) hs s

/-- The first query of every causal history is fixed to the initial point. -/
theorem first_query_one {N : ℕ} (h : bezout.History N) (hN : 0 < N) :
    h.query ⟨0, hN⟩ = 1 := by
  rw [h.query_recurrence]
  simp only [Fin.lt_def, Nat.not_lt_zero, ite_false, Finset.sum_const_zero,
    mul_zero, sub_zero]

/-- No even-horizon history attains both the exact positive-variance additive
MSE optimum and the exact spectral linear optimum, regardless of signs or memory. -/
theorem even_optima_incompatible {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (heven : Even N) (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ) :
    ¬(Risk.mseRisk h I r σ = Risk.mseOptimum I N r σ ∧
      h.spectralGain I = Lower.linearGain I N) := by
  rintro ⟨ha, hl⟩
  let s : Fin N := ⟨0, by omega⟩
  have h₁ := mse_optimal_responses h I he (by omega) r σ hr hσ ha s
  have h₂ := even_linear_optimal_products h I he hN heven hl s
  have hq : (h.query s).eval I.mu = 1 := by rw [first_query_one h (by omega)]; simp
  unfold Lower.physicalKernel at h₂
  rw [hq, mul_one, h₁] at h₂
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq := (div_left_inj' hn).mp h₂
  linarith [derivativeScale_lt_additiveScale I hN]

/-- Even-horizon incompatibility also holds for the actual operator optimum,
with either unrestricted or symmetric perturbations. -/
theorem even_operator_optima_incompatible {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (heven : Even N) (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ) (symmetric : Bool) :
    ¬(Risk.mseRisk h I r σ = Risk.mseOptimum I N r σ ∧
      Gains.operatorGain h I symmetric = Lower.linearGain I N) := by
  rintro ⟨ha, ho⟩
  apply even_optima_incompatible h I he hN heven r σ hr hσ
  refine ⟨ha, le_antisymm ?_ (h.linearGain_le_spectralGain I he hN)⟩
  exact (Gains.spectralGain_le_operatorGain h I symmetric).trans_eq ho

/-- Even-horizon incompatibility also holds for the actual-query relative optimum. -/
theorem even_relative_optima_incompatible {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (heven : Even N) (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ) :
    ¬(Risk.mseRisk h I r σ = Risk.mseOptimum I N r σ ∧
      Gains.localRelativeGain h I = Lower.linearGain I N) := by
  rintro ⟨ha, hl⟩
  apply even_optima_incompatible h I he hN heven r σ hr hσ
  refine ⟨ha, le_antisymm ?_ (h.linearGain_le_spectralGain I he hN)⟩
  exact (Gains.spectralGain_le_localRelativeGain h I).trans_eq hl

end
end bezout.Properties
