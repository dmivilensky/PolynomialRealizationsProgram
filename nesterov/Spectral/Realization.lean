import nesterov.Spectral.Interpolation
import nesterov.IQC.PolynomialSymbols
import nesterov.Rates.Limit

/-! A feasible spectral pair produces one genuine objective and one infinite
stationary history on the real Hilbert space L²(ν;ℂ). The latent history has
exact exponential norm, including modes on which the query polynomial vanishes. -/
noncomputable section
open scoped BigOperators
namespace nesterov.Spectral

/-- The latent wave, whose query and normalized gradient have the prescribed amplitudes. -/
def latent (ν : Spectrum) (t : ℝ) (k : ℕ) : WaveSpace ν :=
  polyak.Waves.mixturePosition ν t (some k)

theorem norm_latent (ν : Spectrum) (t : ℝ) (k : ℕ) :
    ‖latent ν t k‖ = Real.exp (k * t) := polyak.Waves.norm_mixturePosition ν t k

@[simp] theorem norm_latent_zero (ν : Spectrum) (t : ℝ) : ‖latent ν t 0‖ = 1 := by
  simp [norm_latent]

theorem latent_sum (ν : Spectrum) (t : ℝ) (d : ℕ) (a : Fin d → ℝ) (k : ℕ)
    (q : C(Frequency, ℂ))
    (hq : ∀ c, q c = ∑ j, (a j : ℂ) * polyak.Waves.z t (Real.arccos c) ^ j.val) :
    (∑ j, a j • latent ν t (k+j)) =
      lift ν (q * polyak.Waves.positionMap t (some k)) := by
  simp only [latent, polyak.Waves.mixturePosition, ← map_smul, ← map_sum]
  congr 1
  ext c
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    polyak.Waves.positionMap, polyak.Waves.position, ContinuousMap.mul_apply, hq,
    Complex.real_smul, pow_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [ContinuousMap.coe_mk]
  ring

theorem query_latent (M : nesterov.StationaryMethod) (μ L : ℝ)
    (ν : Spectrum) (t : ℝ) (k : ℕ) :
    M.query (latent ν t) k = mixturePosition ν (M.symbolPair μ L t) t (some k) := by
  unfold nesterov.StationaryMethod.query mixturePosition positionMap
  apply latent_sum ν t M.memory M.queryCoeff k
  intro c
  exact M.queryPolynomial_complex_eval _

theorem normalized_latent (M : nesterov.StationaryMethod) (μ L : ℝ)
    (ν : Spectrum) (t : ℝ) (k : ℕ) :
    (∑ j : Fin (M.memory+1), M.normalizedCoeff μ L j • latent ν t (k+j)) =
      mixtureGradient ν (M.symbolPair μ L t) t (some k) := by
  unfold mixtureGradient gradientMap
  apply latent_sum ν t (M.memory+1) (M.normalizedCoeff μ L) k
  intro c
  change ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval _ = _
  rw [M.normalizedPolynomial_eq_sum]
  simp only [Polynomial.eval_map, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  rfl

theorem stateNorm_latent (M : nesterov.StationaryMethod) (ν : Spectrum) (t : ℝ) (k : ℕ) :
    M.stateNorm (latent ν t) k = Real.exp (k*t) * M.stateNorm (latent ν t) 0 := by
  have he (j : Fin M.memory) : Real.exp (((k+j.val : ℕ) : ℝ)*t) =
      Real.exp (k*t) * Real.exp (j.val*t) := by
    rw [Nat.cast_add, add_mul, Real.exp_add]
  have hs : M.stateNorm (latent ν t) k ^ 2 =
      (Real.exp (k*t) * M.stateNorm (latent ν t) 0) ^ 2 := by
    rw [mul_pow, M.stateNorm_sq, M.stateNorm_sq]
    simp only [norm_latent, he, mul_pow, Nat.zero_add, Finset.mul_sum]
  exact (sq_eq_sq₀ (M.stateNorm_nonneg _ _) (mul_nonneg (Real.exp_pos _).le
    (M.stateNorm_nonneg _ _))).mp hs

theorem stateNorm_latent_pos (M : nesterov.StationaryMethod) (ν : Spectrum) (t : ℝ) :
    0 < M.stateNorm (latent ν t) 0 := by
  have h := M.norm_le_stateNorm (latent ν t) 0 ⟨0, M.memory_pos⟩
  simp only [Nat.zero_add, norm_latent_zero] at h
  exact zero_lt_one.trans_le h

/-- Every feasible pair is realized for every nonnegative time by one objective.
Both the function values and its genuine gradient are interpolated exactly. -/
theorem Feasible.exists_objective {M : nesterov.StationaryMethod} {μ L t C : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) {ν : Spectrum}
    (h : Feasible (M.symbolPair μ L t) t ν C) :
    ∃ f : WaveSpace ν → ℝ, polyak.CenteredSmoothStronglyConvex μ L f ∧
      M.IsTrajectory (gradient f) (latent ν t) := by
  obtain ⟨ψ, hψ, hdata⟩ := (mixture_interpolation_iff ν (M.symbolPair μ L t) C t).mpr h
  refine ⟨polyak.denormalizeFunction μ L ψ, hψ.denormalize hμ hμL,
    M.isTrajectory_denormalize hμL hψ.differentiable ?_⟩
  intro k
  rw [normalized_latent, query_latent M μ L]
  exact (hdata (some k)).2.symm

/-- The realized witness belongs to the same unrestricted Hilbert envelope as
all stationary executions, and its entire memory state grows exactly as exp(kt). -/
theorem Feasible.exists_hilbertRun {M : nesterov.StationaryMethod} {μ L t C : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) {ν : Spectrum}
    (h : Feasible (M.symbolPair μ L t) t ν C) :
    ∃ r : nesterov.Rates.HilbertRun M μ L, 0 < r.stateNorm 0 ∧
      ∀ k, r.stateNorm k = Real.exp (k*t) * r.stateNorm 0 := by
  obtain ⟨f, hf, hw⟩ := h.exists_objective hμ hμL
  let r : nesterov.Rates.HilbertRun M μ L := {
    Carrier := WaveSpace ν
    f := f
    admissible := hf
    w := latent ν t
    trajectory := hw }
  exact ⟨r, stateNorm_latent_pos M ν t, stateNorm_latent M ν t⟩

/-- Every feasible exponent bounds the literal worst-case uniform rate from below. -/
theorem Feasible.exp_le_rate {M : nesterov.StationaryMethod} {μ L t C : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) {ν : Spectrum}
    (h : Feasible (M.symbolPair μ L t) t ν C) :
    Real.exp t ≤ nesterov.Rates.rate M μ L := by
  obtain ⟨r, hr, hgrowth⟩ := h.exists_hilbertRun hμ hμL
  apply nesterov.Rates.le_rate_of_pow_le M hμ hμL (Real.exp_pos t).le
  intro k
  have hb := nesterov.Rates.stateNorm_le_envelope r k
  rw [hgrowth k] at hb
  have hx := (mul_le_mul_iff_left₀ hr).mp hb
  simpa only [← Real.exp_nat_mul, mul_comm (k : ℝ) t] using hx

end nesterov.Spectral
