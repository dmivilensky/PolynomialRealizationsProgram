import bezout.Risk.Minimax

/-!
Article: bezout, Theorem 3.1, literal worst-case suprema over actual executions.
Use: identifies the least-universal-bound risk API with the article's supremum
of achieved distances and MSEs across all finite-dimensional admissible models.
Proof: constructors record actual physical executions or probability models;
their upper bounds are exactly the existing universal bound predicates.
-/

namespace bezout.Risk
noncomputable section
open MeasureTheory
open scoped BigOperators
variable {N : ℕ}

/-- An actually achieved additive-error distance in the full comparison class.
Use: the constructor quantifies physical executions, rather than classifying
values indirectly by all universal upper bounds. -/
inductive AdditiveValue (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t : ℝ) : ℝ → Prop where
  | execution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (hH : Analysis.Admissible I H)
      (initial : E) (w : Fin N → E) (hi : ‖initial‖ ≤ r)
      (hw : ∑ s, ‖w s‖ ^ 2 ≤ t ^ 2) (u : h.Execution H initial w) :
      AdditiveValue h I r t ‖u.output‖

/-- An actually achieved martingale MSE in the full probability comparison class.
Use: includes arbitrary probability spaces and adapted dependent errors obeying
the conditional variance budget, exactly as in the article. -/
inductive MseValue (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r σ : ℝ) : ℝ → Prop where
  | model (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E] [mΩ : MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ mΩ)
      (w : ℕ → Ω → E) (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
      (hσ : ∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2)
      (H : E →ₗ[ℝ] E) (hH : Analysis.Admissible I H) (initial : E) (hi : ‖initial‖ ≤ r) :
      MseValue h I r σ (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ)

/-- All distances produced by actual admissible additive-error executions.
Use: the literal domain of the deterministic worst-case supremum. -/
def additiveValues (h : bezout.History N) (I : chebyshev1.SpectralInterval) (r t : ℝ) : Set ℝ :=
  {v | AdditiveValue h I r t v}

/-- All MSEs produced by actual admissible martingale oracle models.
Use: the literal domain of the martingale worst-case supremum. -/
def mseValues (h : bezout.History N) (I : chebyshev1.SpectralInterval) (r σ : ℝ) : Set ℝ :=
  {v | MseValue h I r σ v}

/-- Universal deterministic bounds are exactly upper bounds on actually achieved distances.
Use: makes the supremum interpretation independent of the risk's original definition. -/
theorem additiveValues_upperBounds (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t : ℝ) : upperBounds (additiveValues h I r t) = {C | AdditiveBound h I r t C} := by
  ext C
  constructor
  · intro hb E _ _ _ H hH initial w hi hw u
    exact hb (AdditiveValue.execution E H hH initial w hi hw u)
  · intro hb v hv
    cases hv with
    | execution E H hH initial w hi hw u => exact hb E H hH initial w hi hw u

/-- Universal MSE bounds are exactly upper bounds on actually achieved model MSEs.
Use: all probability and dimension quantifiers agree with the literal article class. -/
theorem mseValues_upperBounds (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r σ : ℝ) : upperBounds (mseValues h I r σ) = {C | MseBound h I r σ C} := by
  ext C
  constructor
  · intro hb E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
    exact hb (MseValue.model E Ω μ 𝓕 w hw hσ H hH initial hi)
  · intro hb v hv
    cases hv with
    | model E Ω μ 𝓕 w hw hσ H hH initial hi => exact hb E Ω μ 𝓕 w hw hσ H hH initial hi

/-- The zero initial state and zero physical errors actually achieve zero distance.
Use: nonemptiness of the literal deterministic risk domain, including zero radii. -/
theorem zero_mem_additiveValues (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t : ℝ) (hr : 0 ≤ r) : 0 ∈ additiveValues h I r t := by
  let H := bezout.History.scalarOperator I.mu
  let u := h.run H 0 (fun _ => 0)
  have hu : ‖u.output‖ = 0 := by rw [h.nominal_output]; simp
  rw [← hu]
  exact AdditiveValue.execution ℝ H
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) 0 (fun _ => 0)
    (by simpa only [norm_zero] using hr) (by simpa using sq_nonneg t) u

/-- A zero martingale on a genuine probability space actually achieves zero MSE.
Use: nonemptiness of the full stochastic risk domain at every variance bound. -/
theorem zero_mem_mseValues (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r σ : ℝ) (hr : 0 ≤ r) : 0 ∈ mseValues h I r σ := by
  let H := bezout.History.scalarOperator I.mu
  have hzero : ∀ s ω, bezout.Probability.Signs.stream N 0 s ω = 0 := by
    intro s ω
    simp [bezout.Probability.Signs.stream, bezout.Probability.Signs.error, bezout.Probability.Signs.value]
  have hout : (∫ ω, ‖h.stochasticOutput H 0 (bezout.Probability.Signs.stream N 0) ω‖ ^ 2
      ∂bezout.Probability.Signs.law N) = 0 := by
    simp only [h.stochasticOutput_response, hzero, map_zero, Finset.sum_const_zero, zero_add,
      norm_zero, zero_pow (by omega : 2 ≠ 0), integral_zero]
  rw [← hout]
  exact MseValue.model ℝ (Fin N → Bool) (bezout.Probability.Signs.law N)
    (bezout.Probability.Signs.past N 0) (bezout.Probability.Signs.stream N 0)
    (bezout.Probability.Signs.martingale N 0)
    (by
      intro s hs
      rw [bezout.Probability.Signs.conditional_variance N 0 s hs]
      exact Filter.Eventually.of_forall (fun _ => by simpa using sq_nonneg σ)) H
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) 0 (by simpa only [norm_zero] using hr)

/-- All actual deterministic risk values form a nonempty bounded set.
Use: validates the real supremum without extended-real exceptional cases. -/
theorem additiveValues_nonempty_bddAbove (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (additiveValues h I r t).Nonempty ∧ BddAbove (additiveValues h I r t) := by
  obtain ⟨C, hC⟩ := additiveBounds_nonempty h I he r t ht
  exact ⟨⟨0, zero_mem_additiveValues h I r t hr⟩,
    ⟨C, by rw [additiveValues_upperBounds]; exact hC⟩⟩

/-- All actual martingale MSE values form a nonempty bounded set.
Use: validates the stochastic real supremum under the exact oracle assumptions. -/
theorem mseValues_nonempty_bddAbove (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (r σ : ℝ) (hr : 0 ≤ r) :
    (mseValues h I r σ).Nonempty ∧ BddAbove (mseValues h I r σ) := by
  obtain ⟨C, hC⟩ := mseBounds_nonempty h I he r σ hr
  exact ⟨⟨0, zero_mem_mseValues h I r σ hr⟩,
    ⟨C, by rw [mseValues_upperBounds]; exact hC⟩⟩

/-- The deterministic risk equals the literal supremum of actual admissible outputs.
Use: exact dictionary from the bound API to the article's worst-case definition. -/
theorem additiveRisk_eq_sSup (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk h I r t = sSup (additiveValues h I r t) := by
  obtain ⟨hne, hbd⟩ := additiveValues_nonempty_bddAbove h I he r t hr ht
  unfold additiveRisk
  rw [← additiveValues_upperBounds]
  exact csInf_upperBounds_eq_csSup hbd hne

/-- The martingale MSE risk equals the literal supremum over all actual models.
Use: the article's variance and causality quantifiers are preserved exactly. -/
theorem mseRisk_eq_sSup (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (he : h.ChebyshevExact I) (r σ : ℝ) (hr : 0 ≤ r) :
    mseRisk h I r σ = sSup (mseValues h I r σ) := by
  obtain ⟨hne, hbd⟩ := mseValues_nonempty_bddAbove h I he r σ hr
  unfold mseRisk
  rw [← mseValues_upperBounds]
  exact csInf_upperBounds_eq_csSup hbd hne

end
end bezout.Risk
