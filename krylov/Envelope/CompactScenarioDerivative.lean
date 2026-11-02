import krylov.Envelope.JointScenarioOutput
import krylov.Envelope.CompactNormVariation
import krylov.Stability.CanonicalContinuity

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm, actual compact-uniform source derivative budgets.
Use: bound true canonical source first variations uniformly over genuine
compact reference sets with the real initial-error weight.
Source: primitive-derived actual joint cycle regularity and the existing
weighted compact Frechet derivative bound on the genuine zero-scenario slice.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- Every actual smooth source method has a genuine compact-uniform canonical scenario derivative bound weighted by the true initial error.
Use: Every actual smooth source method has a genuine compact-uniform canonical scenario derivative bound weighted by the true initial error.
Article: main_krylov, cor:lm, actual compact-uniform source derivative budgets.
Proof: Apply the existing real weighted derivative bound to the genuine joint cycle on the actual compact zero-scenario slice; evaluate true reference-preserving directions and identify the real scenario derivative. -/
theorem compact_scenario_derivative_bound (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ J : ℝ, 0≤J ∧ ∀ x∈K, ∀ Θ : CanonicalScenario n N,
      ‖scenarioCanonicalDerivative M.policy (base x) (g x) N Θ‖≤
        J*‖Θ‖*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Bound the real joint output derivative on the genuine compact reference slice with its actual positive initial-error weight.
  let Φ := jointScenarioOutput M.policy base g N
  let e0 := fun x => ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
  let K0 : Set (X × CanonicalScenario n N) := K×ˢ{0}
  have hbasepos (x : X) (hx : x∈K) : (base x).PosDef := (hpos x hx).self_of_nhds
  have hgnz (x : X) (hx : x∈K) : g x≠0 := cg_nonstagnation _ (hbasepos x hx) _ 0 (hN.trans_le (hcount x hx))
  have hΦ : ∀ p∈K0, ContDiffAt ℝ 2 Φ p := by
    rintro ⟨x,Θ⟩ ⟨hx,hΘ⟩
    have hz : Θ=0 := Set.mem_singleton_iff.mp hΘ
    subst Θ
    exact jointScenarioOutput_regular M base g x (hb x hx) (hpos x hx) (hg x hx) (hcount x hx)
  have he0 : ContinuousOn e0 K := canonical_error_continuousOn base g K
    (fun x hx => (hb x hx).continuousAt.continuousWithinAt) (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hbasepos
  -- The existing genuine compact derivative estimate is independent of every actual scenario and budget profile.
  obtain ⟨J,hJ,hj⟩ := compact_weighted_first_derivative Φ (fun p => e0 p.1) K0
    (hK.prod isCompact_singleton) hΦ (he0.comp continuous_fst.continuousOn (fun _ hp => hp.1))
    (fun p hp => canonical_error_pos _ (hbasepos _ hp.1) _ (hgnz _ hp.1))
  refine ⟨J,hJ,?_⟩
  intro x hx Θ
  have hn : ‖((0 : X),Θ)‖=‖Θ‖ := by
    change max ‖(0 : X)‖ ‖Θ‖=‖Θ‖
    rw [_root_.norm_zero,max_eq_right (norm_nonneg Θ)]
  have hh := hj (x,0) ⟨hx,rfl⟩ (0,Θ)
  rw [jointScenarioOutput_scenario_derivative M base g x (hb x hx) (hpos x hx) (hg x hx) (hcount x hx) Θ,hn] at hh
  exact hh
end
end krylov.Envelope
