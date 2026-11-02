import krylov.Envelope.JointScenarioOutput
import krylov.Envelope.ScenarioRealizationMinimax
import krylov.Stability.SmoothMetricCompact

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, actual compact-uniform finite-scenario remainder.
Use: obtain a genuine common quadratic Taylor tube for true source scenarios
and varying compact references, with the actual initial-error factor.
Source: primitive-derived actual joint source-cycle regularity, existing
weighted compact-reference Taylor calculus and genuine canonical filtration.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Every actual smooth source method has a genuine compact-uniform finite-scenario vector envelope with its true initial-error weighted quadratic remainder.
Use: Every actual smooth source method has a genuine compact-uniform finite-scenario vector envelope with its true initial-error weighted quadratic remainder.
Article: main_krylov, thm:E and s3:cor:qn, actual compact-uniform finite-scenario remainder.
Proof: Use the real joint reference/scenario cycle and the existing compact-reference weighted Taylor theorem. Genuine active reference data make the weight positive. Identify the actual zero-scenario execution with CG and its real scenario derivative with the proved common-unexplored plus explored variation. -/
theorem compact_scenario_taylor (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ Θ : CanonicalScenario n N, ‖Θ‖≤δ →
      ‖cgOperator (metricRoot (base x))⁻¹ (scenarioGradient M.policy (base x) (g x) N Θ)-
        (cgCanonicalError (base x) (g x) N+scenarioUnexplored (base x) (g x) N Θ+
          scenarioVariation M.policy (base x) (g x) N Θ)‖≤
            C*‖Θ‖^2*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Apply the existing common compact reference tube to the genuinely executed joint source-cycle output.
  let Φ := jointScenarioOutput M.policy base g N
  let U := interior {p | ContDiffAt ℝ 2 Φ p}
  have hΦ (x : X) (hx : x∈K) : ContDiffAt ℝ 2 Φ (x,0) :=
    jointScenarioOutput_regular M base g x (hb x hx) (hpos x hx) (hg x hx) (hcount x hx)
  have hKU : ∀ x∈K, (x,(0 : CanonicalScenario n N))∈U := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr ((hΦ x hx).eventually (by simp))
  have hbasepos (x : X) (hx : x∈K) : (base x).PosDef := (hpos x hx).self_of_nhds
  have hgnz (x : X) (hx : x∈K) : g x≠0 := cg_nonstagnation _ (hbasepos x hx) _ 0 (hN.trans_le (hcount x hx))
  -- Retain the actual positive initial-error weight uniformly on the true compact reference family.
  obtain ⟨δ,C,hδ,hC,ht⟩ := compact_reference_taylor Φ
    (fun x => ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖) 2 U K isOpen_interior hK hKU
    (fun p hp => (show ContDiffAt ℝ 2 Φ p from interior_subset hp).contDiffWithinAt)
    (canonical_error_continuousOn base g K (fun x hx => (hb x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hbasepos)
    (fun x hx => canonical_error_pos (base x) (hbasepos x hx) (g x) (hgnz x hx))
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx Θ hΘ
  -- Identify the real zero-scenario execution and true reference-preserving derivative before rewriting the genuine Taylor polynomial.
  have href : Φ (x,0)=cgCanonicalError (base x) (g x) N := by
    change cgOperator (metricRoot (base x))⁻¹ (probedGradient M.policy
      (scenarioProbe (base x) 0) (scenarioCorrection (base x) 0) (g x) N)=_
    rw [scenarioProbe_zero,scenarioCorrection_zero]
    exact congrArg (cgOperator (metricRoot (base x))⁻¹)
      (quadratic_gradient_eq_cg M.policy M.consistent _ (cgOperator_positive _ (hbasepos x hx)).1
        (cgOperator_positive _ (hbasepos x hx)).2 (g x) N)
  have hD : fderiv ℝ Φ (x,0) (0,Θ)=scenarioCanonicalDerivative M.policy (base x) (g x) N Θ :=
    jointScenarioOutput_scenario_derivative M base g x (hb x hx) (hpos x hx) (hg x hx) (hcount x hx) Θ
  have hT : taylorPolynomial Φ 2 (x,0) (0,Θ)=cgCanonicalError (base x) (g x) N+
      scenarioUnexplored (base x) (g x) N Θ+scenarioVariation M.policy (base x) (g x) N Θ := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply]
    simp only [Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,href,hD]
    rw [scenarioCanonicalDerivative_split M (base x) (hbasepos x hx) (g x) N (hcount x hx) Θ]
    abel
  have hh := ht x hx Θ hΘ 2 (by omega) le_rfl
  rw [hT] at hh
  exact hh
end
end krylov.Envelope
