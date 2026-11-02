import bezout.Gains.RelativeRisk

/-!
Article: bezout, Theorem 4.1, supremum before the positive-scale upper limit.
Use: the finite-scale risk is the literal supremum of deviations achieved by
actual noisy-query executions in every finite-dimensional admissible model.
Proof: actual-execution constructors have exactly the universal bound predicate
as their upper bounds; finite majorants justify the real supremum.
-/

namespace bezout.Gains
noncomputable section
open Polynomial Filter Topology
open scoped BigOperators
variable {N : ℕ}

/-- A relative-error deviation achieved by an actual admissible physical execution.
Use: records the dimension, Hessian, actual queries, errors and temporal budget,
without defining achieved values through the family of all upper bounds. -/
inductive RelativeValue (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t : ℝ) : ℝ → Prop where
  | execution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (hH : Analysis.Admissible I H)
      (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
      (δ : Fin N → ℝ) (hi : ‖initial‖ ≤ 1)
      (hw : Analysis.RelativeErrors h H initial noise u t δ) :
      RelativeValue h I t ‖u.output - (aeval H h.terminal) initial‖

/-- All deviations actually attained at one fixed relative-error scale.
Use: the domain of the supremum taken before the local limit. -/
def relativeValues (h : bezout.History N) (I : chebyshev1.SpectralInterval) (t : ℝ) : Set ℝ :=
  {v | RelativeValue h I t v}

/-- Finite-scale universal bounds are exactly upper bounds on actual achieved deviations.
Use: identifies the literal supremum with the existing bound API. -/
theorem relativeValues_upperBounds (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t : ℝ) : upperBounds (relativeValues h I t) = {C | RelativeBound h I t C} := by
  ext C
  constructor
  · intro hb E _ _ _ H hH initial noise u δ hi hw
    exact hb (RelativeValue.execution E H hH initial noise u δ hi hw)
  · intro hb v hv
    cases hv with
    | execution E H hH initial noise u δ hi hw => exact hb E H hH initial noise u δ hi hw

/-- The zero physical execution attains zero relative deviation at every scale.
Use: includes degenerate zero-error and zero-initial-state models. -/
theorem zero_mem_relativeValues (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t : ℝ) : 0 ∈ relativeValues h I t := by
  let H := bezout.History.scalarOperator I.mu
  let u := h.run H 0 (fun _ => 0)
  have hu : ‖u.output - (aeval H h.terminal) 0‖ = 0 := by rw [h.nominal_output]; simp
  rw [← hu]
  exact RelativeValue.execution ℝ H
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) 0 (fun _ => 0) u
    (fun _ => 0) (by simp) ⟨by simp, by simp, by simp⟩

/-- Every fixed-scale set of actual relative deviations is nonempty and bounded.
Use: the finite real supremum precedes the positive-scale limit. -/
theorem relativeValues_nonempty_bddAbove (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (t : ℝ) :
    (relativeValues h I t).Nonempty ∧ BddAbove (relativeValues h I t) := by
  obtain ⟨C, hC⟩ := relativeBounds_nonempty h I t
  exact ⟨⟨0, zero_mem_relativeValues h I t⟩,
    ⟨C, by rw [relativeValues_upperBounds]; exact hC⟩⟩

/-- The actual finite-scale relative risk is the supremum of achieved deviations.
Use: literal correspondence to the article's worst-case relative execution risk. -/
theorem relativeRisk_eq_sSup (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t : ℝ) : relativeRisk h I t = sSup (relativeValues h I t) := by
  obtain ⟨hne, hbd⟩ := relativeValues_nonempty_bddAbove h I t
  unfold relativeRisk
  rw [← relativeValues_upperBounds]
  exact csInf_upperBounds_eq_csSup hbd hne

/-- The local gain takes the supremum over actual dimensions and streams before
its literal positive-scale upper limit, exactly in the article's order. -/
theorem localRelativeGain_eq_limsup_sSup (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) :
    localRelativeGain h I =
      Filter.limsup (fun t => sSup (relativeValues h I t) / t) (𝓝[>] (0 : ℝ)) := by
  rw [localRelativeGain_eq_limsup]
  congr 1
  funext t
  rw [relativeRisk_eq_sSup]

end
end bezout.Gains
