import bezout.Risk.Lower

/-!
Article: bezout, Theorem 3.1, exact dimension-uniform risk definitions.
Use: the risks are the infima of all bounds valid for actual executions in
every finite real Hilbert space. Thus the supremum over dimensions and
admissible Hessians is included, rather than fixed in advance.
Proof: every history has finite response bounds; the scalar attaining
examples force the lower constants. Equal uniform responses attain both.
-/

namespace bezout.Risk
noncomputable section
open MeasureTheory
open scoped BigOperators
variable {N : ℕ}

/-- A universal upper bound on the actual deterministic additive risk. -/
def AdditiveBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t C : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E), Analysis.Admissible I H →
    ∀ (initial : E) (w : Fin N → E), ‖initial‖ ≤ r → (∑ s, ‖w s‖ ^ 2 ≤ t ^ 2) →
      ∀ u : h.Execution H initial w, ‖u.output‖ ≤ C

/-- The worst-case additive distance, over dimensions, Hessians, initial states
and physical error streams, expressed as the least universal upper bound. -/
def additiveRisk (h : bezout.History N) (I : chebyshev1.SpectralInterval) (r t : ℝ) : ℝ :=
  sInf {C : ℝ | AdditiveBound h I r t C}

/-- A universal MSE bound under the article's actual martingale assumptions. -/
def MseBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r σ C : ℝ) : Prop :=
  ∀ (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ mΩ)
    (w : ℕ → Ω → E), bezout.Probability.MartingaleDifferences N 𝓕 w μ →
    (∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2) →
    ∀ (H : E →ₗ[ℝ] E), Analysis.Admissible I H →
      ∀ initial : E, ‖initial‖ ≤ r → (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) ≤ C

/-- The worst-case martingale MSE is the least bound on all actual admissible models. -/
def mseRisk (h : bezout.History N) (I : chebyshev1.SpectralInterval) (r σ : ℝ) : ℝ :=
  sInf {C : ℝ | MseBound h I r σ C}

/-- The sharp deterministic value stated in Theorem 3.1. -/
def additiveOptimum (I : chebyshev1.SpectralInterval) (N : ℕ) (r t : ℝ) : ℝ :=
  I.epsilon N * r + t * Lower.additiveScale I N / Real.sqrt N

/-- The sharp martingale MSE value stated in Theorem 3.1. -/
def mseOptimum (I : chebyshev1.SpectralInterval) (N : ℕ) (r σ : ℝ) : ℝ :=
  I.epsilon N ^ 2 * r ^ 2 + σ ^ 2 * Lower.additiveScale I N ^ 2 / N

/-- Every fixed history has finite nonnegative scalar response bounds. -/
theorem exists_responseBounds (h : bezout.History N) (I : chebyshev1.SpectralInterval) :
    ∃ P, ResponseBounds h I P := by
  choose P hP hp using fun s : Fin N => Analysis.exists_polynomial_bound I (h.response s)
  exact ⟨P, hP, hp⟩

/-- Every exact finite history has a finite deterministic worst-case risk. -/
theorem additiveBounds_nonempty (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (r t : ℝ) (ht : 0 ≤ t) :
    {C : ℝ | AdditiveBound h I r t C}.Nonempty := by
  obtain ⟨P, hP⟩ := exists_responseBounds h I
  refine ⟨I.epsilon N * r + t * Analysis.energyNorm P, ?_⟩
  intro E _ _ _ H hH initial w hi hw u
  exact additive_upper h I he H hH P hP initial w r t ht hi hw u

/-- Every exact finite history has a finite worst-case martingale MSE. -/
theorem mseBounds_nonempty (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (r σ : ℝ) (hr : 0 ≤ r) :
    {C : ℝ | MseBound h I r σ C}.Nonempty := by
  obtain ⟨P, hP⟩ := exists_responseBounds h I
  refine ⟨I.epsilon N ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, P s ^ 2, ?_⟩
  intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
  exact mse_upper h I he H hH P hP initial hw r σ hr hi hσ

/-- No universal deterministic bound can improve the scalar endpoint obstruction. -/
theorem additiveBound_lower (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r t C : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hb : AdditiveBound h I r t C) : additiveOptimum I N r t ≤ C := by
  obtain ⟨w, hw, hout⟩ := scalar_additive_attainment h I he r t hr ht
  have hu := hb ℝ (bezout.History.scalarOperator I.mu)
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) r w
    (by simp [Real.norm_eq_abs, abs_of_nonneg hr]) hw (h.run _ r w)
  rw [hout] at hu
  have hl := mul_le_mul_of_nonneg_left (additive_endpoint_norm h I he hN) ht
  exact (show additiveOptimum I N r t ≤ _ by
    simpa only [additiveOptimum, mul_div_assoc] using add_le_add (le_refl (I.epsilon N * r)) hl).trans hu

/-- No universal martingale bound can improve the fair-sign endpoint example. -/
theorem mseBound_lower (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r σ C : ℝ) (hr : 0 ≤ r)
    (hb : MseBound h I r σ C) : mseOptimum I N r σ ≤ C := by
  have hu := hb ℝ (Fin N → Bool) (bezout.Probability.Signs.law N)
    (bezout.Probability.Signs.past N σ) (bezout.Probability.Signs.stream N σ)
    (bezout.Probability.Signs.martingale N σ)
    (fun s hs => by rw [bezout.Probability.Signs.conditional_variance N σ s hs])
    (bezout.History.scalarOperator I.mu)
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) r
    (by simp [Real.norm_eq_abs, abs_of_nonneg hr])
  rw [scalar_mse_attainment h I he r σ] at hu
  have hl := mul_le_mul_of_nonneg_left (additive_endpoint_energy h I he hN) (sq_nonneg σ)
  exact (show mseOptimum I N r σ ≤ _ by
    simpa only [mseOptimum, mul_div_assoc] using
      add_le_add (le_refl (I.epsilon N ^ 2 * r ^ 2)) hl).trans hu

/-- The unrestricted deterministic risk is at least the sharp value. -/
theorem additiveRisk_lower (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveOptimum I N r t ≤ additiveRisk h I r t :=
  le_csInf (additiveBounds_nonempty h I he r t ht)
    (fun C hb => additiveBound_lower h I he hN r t C hr ht hb)

/-- The unrestricted martingale risk is at least the sharp value. -/
theorem mseRisk_lower (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r σ : ℝ) (hr : 0 ≤ r) :
    mseOptimum I N r σ ≤ mseRisk h I r σ :=
  le_csInf (mseBounds_nonempty h I he r σ hr)
    (fun C hb => mseBound_lower h I he hN r σ C hr hb)

end
end bezout.Risk
