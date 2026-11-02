import krylov.Envelope.JointScenarioOutput
import krylov.Stability.CanonicalContinuity

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm, actual compact before-exhaustion reference gap.
Use: derive true reference-error continuity and the genuine compact bound
on initial error divided by final reference error before actual exhaustion.
Source: actual primitive-derived joint cycle regularity, genuine global
quadratic CG consistency, true active-count nonstagnation and compactness.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The genuine zero-scenario joint output of every actual globally CG-consistent method is the true canonical CG reference error.
Use: The genuine zero-scenario joint output of every actual globally CG-consistent method is the true canonical CG reference error.
Article: main_krylov, cor:lm, actual compact before-exhaustion reference gap.
Proof: The actual source zero scenario has the true constant quadratic segment operators; use genuine quadratic consistency. -/
theorem jointScenarioOutput_zero (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (x : X) (hb : (base x).PosDef) (N : ℕ) :
    jointScenarioOutput m base g N (x,0)=cgCanonicalError (base x) (g x) N := by
  change cgOperator (metricRoot (base x))⁻¹ (probedGradient m
    (scenarioProbe (base x) 0) (scenarioCorrection (base x) 0) (g x) N)=_
  rw [scenarioProbe_zero,scenarioCorrection_zero]
  exact congrArg (cgOperator (metricRoot (base x))⁻¹)
    (quadratic_gradient_eq_cg m hm _ (cgOperator_positive _ hb).1 (cgOperator_positive _ hb).2 (g x) N)

/-- The actual canonical CG reference error is continuous on every genuine active smooth reference family.
Use: The actual canonical CG reference error is continuous on every genuine active smooth reference family.
Article: main_krylov, cor:lm, actual compact before-exhaustion reference gap.
Proof: Restrict the real jointly smooth method output to its genuine zero-scenario slice and identify the actual quadratic execution with true CG. -/
theorem referenceCanonicalError_continuousOn (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N≤referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ContinuousOn (fun x => cgCanonicalError (base x) (g x) N) K := by
  -- The genuine zero-scenario slice is continuous, and actual global quadratic consistency identifies it with the true CG reference error.
  have hc : ContinuousOn (fun x => jointScenarioOutput M.policy base g N (x,0)) K := by
    intro x hx
    have hs : ContinuousAt (fun y : X => (y,(0 : CanonicalScenario n N))) x :=
      continuousAt_id.prodMk continuousAt_const
    have ht : ContinuousAt (fun y => jointScenarioOutput M.policy base g N (y,0)) x :=
      (jointScenarioOutput_regular M base g x (hb x hx) (hpos x hx) (hg x hx) (hcount x hx)).continuousAt.comp (f := fun y : X => (y,(0 : CanonicalScenario n N))) hs
    exact ht.continuousWithinAt
  apply hc.congr
  intro x hx
  exact (jointScenarioOutput_zero M.policy M.consistent base g x (hpos x hx).self_of_nhds N).symm

/-- On every genuine compact strictly-before-exhaustion reference family the true initial-to-final canonical error norm ratio has a real finite uniform bound.
Use: On every genuine compact strictly-before-exhaustion reference family the true initial-to-final canonical error norm ratio has a real finite uniform bound.
Article: main_krylov, cor:lm, actual compact before-exhaustion reference gap.
Proof: Actual active-count nonstagnation and positive inverse metric give a strictly positive true final error. Its genuine continuity makes the real ratio continuous on the actual compact set, so it has a true finite bound. -/
theorem compact_reference_error_ratio_bound (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hg : ∀ x∈K, ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K), N<referenceAtomCount (base x) ((hpos x hx).self_of_nhds) (g x)) :
    ∃ C : ℝ, 0≤C ∧ ∀ x∈K,
      ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖/‖cgCanonicalError (base x) (g x) N‖≤C := by
  -- Genuine strict activity makes every real final reference norm positive before taking the actual compact ratio bound.
  have hfinal (x : X) (hx : x∈K) : 0<‖cgCanonicalError (base x) (g x) N‖ :=
    canonical_error_pos _ (hpos x hx).self_of_nhds _ (cg_nonstagnation _ (hpos x hx).self_of_nhds _ N (hcount x hx))
  have he0 := canonical_error_continuousOn base g K
    (fun x hx => (hb x hx).continuousAt.continuousWithinAt) (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hpos x hx).self_of_nhds)
  have he := (referenceCanonicalError_continuousOn M base g N K hb hpos hg (fun x hx => (hcount x hx).le)).norm
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (he0.div he (fun x hx => (hfinal x hx).ne'))
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have hh := hC x hx
  rw [Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans (hh.trans (le_max_left _ _))
end
end krylov.Envelope
