import krylov.Envelope.JointScenarioOutput
import krylov.Envelope.CompactNormVariation
import krylov.Envelope.ActualScenarioNorm

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and cor:lm, actual common scenario norm first variation.
Use: give the true compact-uniform canonical finite-output norm expansion
with its real common unexplored linear term and explicit exhaustion factor.
Source: proved actual joint source-cycle regularity, existing weighted
Hilbert norm Taylor calculus and genuine CG explored/complement orthogonality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The genuine compact-uniform actual output norm expansion has the real common unexplored first variation and the true quadratic initial-error remainder with its explicit near-exhaustion factor.
Use: The genuine compact-uniform actual output norm expansion has the real common unexplored first variation and the true quadratic initial-error remainder with its explicit near-exhaustion factor.
Article: main_krylov, thm:E and cor:lm, actual common scenario norm first variation.
Proof: Apply the existing actual weighted norm variation theorem to the genuine joint source cycle on the true compact zero-scenario slice. Identify the real derivative by the actual canonical filtration, and remove its genuine explored pairing using true CG orthogonality. -/
theorem compact_scenario_norm_variation (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 0<N) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ Θ : CanonicalScenario n N, ‖Θ‖≤δ →
      let e := cgCanonicalError (base x) (g x) N
      let e0 := ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
      0<‖e‖ →
      |actualScenarioNorm M.policy (base x) (g x) N Θ-‖e‖-
        inner ℝ e (scenarioUnexplored (base x) (g x) N Θ)/‖e‖|≤C*‖Θ‖^2*e0*(1+e0/‖e‖) := by
  -- Use the actual joint execution on the genuine zero-scenario compact slice with its true initial-error weight.
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
  have he : ContinuousOn (fun p : X × CanonicalScenario n N => e0 p.1) K0 :=
    he0.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hep : ∀ p∈K0, 0<e0 p.1 := fun p hp => canonical_error_pos _ (hbasepos _ hp.1) _ (hgnz _ hp.1)
  -- Retain the genuine common Taylor radius even when real final reference errors become small.
  obtain ⟨δ,C,hδ,hC,ht⟩ := compact_weighted_norm_variation Φ (fun p => e0 p.1) K0
    (hK.prod isCompact_singleton) hΦ he hep
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx Θ hΘ e e₀ ha
  have hn : ‖((0 : X),Θ)‖=‖Θ‖ := by
    change max ‖(0 : X)‖ ‖Θ‖=‖Θ‖
    rw [_root_.norm_zero,max_eq_right (norm_nonneg Θ)]
  have href : Φ (x,0)=e := by
    change cgOperator (metricRoot (base x))⁻¹ (probedGradient M.policy
      (scenarioProbe (base x) 0) (scenarioCorrection (base x) 0) (g x) N)=_
    rw [scenarioProbe_zero,scenarioCorrection_zero]
    exact congrArg (cgOperator (metricRoot (base x))⁻¹)
      (quadratic_gradient_eq_cg M.policy M.consistent _ (cgOperator_positive _ (hbasepos x hx)).1
        (cgOperator_positive _ (hbasepos x hx)).2 (g x) N)
  have hD : fderiv ℝ Φ (x,0) (0,Θ)=scenarioCanonicalDerivative M.policy (base x) (g x) N Θ :=
    jointScenarioOutput_scenario_derivative M base g x (hb x hx) (hpos x hx) (hg x hx) (hcount x hx) Θ
  -- True CG orthogonality kills the actual explored derivative in the real first norm variation.
  have ho : inner ℝ e (scenarioVariation M.policy (base x) (g x) N Θ)=0 := by
    rw [real_inner_comm]
    exact exploredFlag_error_orthogonal (base x) (hbasepos x hx) (g x) (hcount x hx) _
      ((exploredFlag (base x) (g x) N).starProjection_apply_mem _)
  have hh := ht (x,0) ⟨hx,rfl⟩ (0,Θ) (hn ▸ hΘ) (by rw [href];exact ha)
  rw [href,hD,scenarioCanonicalDerivative_split M (base x) (hbasepos x hx) (g x) N (hcount x hx) Θ,
    inner_add_right,ho,add_zero] at hh
  simpa only [Prod.mk_add_mk,add_zero,zero_add,hn,Φ,jointScenarioOutput,actualScenarioNorm,e₀,e0] using hh
end
end krylov.Envelope
