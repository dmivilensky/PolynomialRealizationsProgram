import krylov.Envelope.CompactScenarioNormVariation
import krylov.Envelope.ReferenceErrorContinuity

set_option autoImplicit false
/-!
Article: Corollary B.14 [cor:lm] of krylov.tex.
Use: compare actual smooth-method gradient norms with the real common
source first variation removed, explicitly retaining the true near-
exhaustion ratio and deriving the genuine uniform rate before exhaustion.
Source: actual common scenario norm variation, genuine finite budget
norm bounds and true compact initial-to-final reference error ratio bounds.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator NNReal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Any two actual smooth source methods have a genuine compact-uniform largest-budget-squared norm comparison with the true explicit initial-to-final reference error ratio.
Use: Any two actual smooth source methods have a genuine compact-uniform largest-budget-squared norm comparison with the true explicit initial-to-final reference error ratio.
Article: main_krylov, cor:lm, actual compact-uniform quadratic budget comparison.
Proof: Their real common unexplored first norm variations cancel exactly. Add the two actual norm Taylor remainders and enlarge the true scenario norm to the genuine budget radius. -/
theorem compact_budget_method_comparison (M L : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ ω : Fin (N-1) → ℝ≥0,
      (maximalBudget ω : ℝ)≤δ → ∀ Θ∈scenarioBudget N ω,
      0<‖cgCanonicalError (base x) (g x) N‖ →
      |actualScenarioNorm M.policy (base x) (g x) N Θ-actualScenarioNorm L.policy (base x) (g x) N Θ|≤
        C*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖*
          (1+‖cgOperator (metricRoot (base x))⁻¹ (g x)‖/‖cgCanonicalError (base x) (g x) N‖) := by
  -- The two true output norm expansions have exactly the same genuine first variation on each real source scenario.
  obtain ⟨δM,CM,hδM,hCM,hM⟩ := compact_scenario_norm_variation M base g N hN K hK hb hpos hg hcount
  obtain ⟨δL,CL,hδL,hCL,hL⟩ := compact_scenario_norm_variation L base g N hN K hK hb hpos hg hcount
  refine ⟨min δM δL,CM+CL,lt_min hδM hδL,add_nonneg hCM hCL,?_⟩
  intro x hx ω hω Θ hΘ ha
  have hn := scenarioBudget_norm_le ω Θ hΘ
  have hm := hM x hx Θ (hn.trans (hω.trans (min_le_left _ _))) ha
  have hl := hL x hx Θ (hn.trans (hω.trans (min_le_right _ _))) ha
  -- Cancel the actual common linear norm term before enlarging only the genuine scenario remainder radius.
  let a := ‖cgCanonicalError (base x) (g x) N‖
  let e0 := ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
  let t := inner ℝ (cgCanonicalError (base x) (g x) N) (scenarioUnexplored (base x) (g x) N Θ)/a
  have heq : actualScenarioNorm M.policy (base x) (g x) N Θ-actualScenarioNorm L.policy (base x) (g x) N Θ=
      (actualScenarioNorm M.policy (base x) (g x) N Θ-a-t)-
      (actualScenarioNorm L.policy (base x) (g x) N Θ-a-t) := by ring
  rw [heq]
  apply (abs_sub _ _).trans ((add_le_add hm hl).trans _)
  calc
    _ =(CM+CL)*‖Θ‖^2*e0*(1+e0/a) := by ring
    _ ≤(CM+CL)*(maximalBudget ω : ℝ)^2*e0*(1+e0/a) := by
      gcongr

/-- On every genuine compact strictly-before-exhaustion reference family, actual smooth-method output norms differ by a true uniform largest-budget-squared initial-error bound.
Use: On every genuine compact strictly-before-exhaustion reference family, actual smooth-method output norms differ by a true uniform largest-budget-squared initial-error bound.
Article: main_krylov, cor:lm, actual compact-uniform quadratic budget comparison.
Proof: The genuine compact reference error ratio is bounded; substitute its real uniform bound in the proved actual common-first-variation comparison. -/
theorem compact_budget_method_quadratic (M L : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N<referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ ω : Fin (N-1) → ℝ≥0,
      (maximalBudget ω : ℝ)≤δ → ∀ Θ∈scenarioBudget N ω,
      |actualScenarioNorm M.policy (base x) (g x) N Θ-actualScenarioNorm L.policy (base x) (g x) N Θ|≤
        C*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Strict genuine reference activity supplies a real compact error-ratio bound, independent of the actual budget profile.
  obtain ⟨δ,C,hδ,hC,ht⟩ := compact_budget_method_comparison M L base g N hN K hK hb hpos hg (fun x hx => (hcount x hx).le)
  obtain ⟨J,hJ,hj⟩ := compact_reference_error_ratio_bound M base g N K hK hb hpos hg hcount
  refine ⟨δ,C*(1+J),hδ,mul_nonneg hC (by positivity),?_⟩
  intro x hx ω hω Θ hΘ
  have ha : 0<‖cgCanonicalError (base x) (g x) N‖ :=
    canonical_error_pos _ (hpos x hx).self_of_nhds _ (cg_nonstagnation _ (hpos x hx).self_of_nhds _ N (hcount x hx))
  apply (ht x hx ω hω Θ hΘ ha).trans
  calc
    _ ≤C*(maximalBudget ω : ℝ)^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖*(1+J) := by
      gcongr
      exact hj x hx
    _ = _ := by ring
end
end krylov.Envelope
