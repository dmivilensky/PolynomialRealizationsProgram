import krylov.Envelope.AbsorbedShadow
import krylov.Envelope.FiniteObservationJets

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), genuine complete observed absorbed information fibre.
Use: prove every actual observation and recorded-step coordinate has
the true first derivative of the same globally CG-consistent policy
on one genuinely positive single-quadratic shadow.
Source: genuine moving-shadow whole-history execution and the actual
primitive-derived full-observation finite oracle first-jet transfer.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability Filter Topology
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every actual full-history observation coordinate on genuine symmetric absorbed changing-operator scenarios has the same true first derivative as its real single-quadratic shadow execution.
Use: Every actual full-history observation coordinate on genuine symmetric absorbed changing-operator scenarios has the same true first derivative as its real single-quadratic shadow execution.
Article: main_krylov, apB:lem:mu(c), genuine complete observed absorbed information fibre.
Proof: Derive the actual moving CG compression regularity and true absorbed operator first jets. Genuine finite-oracle differentiation transfers every real observation coordinate, and exact actual whole-history quadratic-shadow execution identifies its true single-quadratic first jet. -/
theorem actual_absorbed_shadow_observation (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : ℝ → E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hQ : (Q 0).toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q 0 v))
    (hpre : ∀ i<N, CG.gradient (Q 0) g i≠0) (hsmooth : SmoothProbedCycleAt m 2 (Q 0) g N)
    (haQ : AnalyticAt ℝ Q 0) (hdQ : HasDerivAt Q (∑ l∈Finset.range (N-1),D l) 0)
    (hgood : ∀ᶠ t in 𝓝 (0 : ℝ), (Q t).toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q t v)) ∧ ∀ i<N, CG.gradient (Q t) g i≠0)
    (hD : ∀ l<N-1, (D l).toLinearMap.IsSymmetric)
    (hkill : ∀ l<N-1, ∀ i≤l, D l (CG.gradient (Q 0) g i)=0)
    (B : ℝ → ℕ → E →L[ℝ] E) (hB0 : B 0=fun _ => Q 0)
    (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) (j : ℕ) :
    deriv (fun t => (methodRun m (cumulativeOraclePath (Q 0) D t) (B t) g N).observationList.getD j 0) 0=
      deriv (fun t => (methodRun m (fun _ => Q t) (fun _ => Q t) g N).observationList.getD j 0) 0 := by
  -- Actual moving CG regularity derives the true absorbed operator first jets before transferring every genuine observation coordinate.
  have hG (i : ℕ) (hi : i<N) : ContDiffAt ℝ 2 (fun t => CG.gradient (Q t) g i) 0 :=
    (cg_prefix_analytic Q (fun _ => g) 0 haQ analyticAt_const hQ hpos i (fun j hj => hpre j (hj.trans hi))).1.contDiffAt
  have hS0 : shadowSegments Q D g N 0=fun _ => Q 0 := funext (fun k => shadowSegments_zero Q D g N k)
  have htransfer := actual_observation_firstJet_transfer m hm (Q 0) hQ hpos g N hpre hsmooth
    (cumulativeOraclePath (Q 0) D) B (shadowSegments Q D g N) B
    (fun k => ∑ l∈Finset.range k,D l) (fun k => deriv (fun t => B t k) 0)
    (cumulativeOraclePath_zero (Q 0) D) hB0 hS0 hB0
    (fun i _ => cumulativeOraclePath_hasDeriv (Q 0) D i) (fun i hi => (hB i hi).hasDerivAt)
    (fun i hi => shadowSegments_hasDeriv Q D g N i hi hdQ hG hpre hD hkill) (fun i hi => (hB i hi).hasDerivAt) j
  -- On the genuine active positive neighborhood the complete real histories agree, including every actual correction answer and recorded step.
  have hshadow : (fun t => (methodRun m (shadowSegments Q D g N t) (B t) g N).observationList.getD j 0)=ᶠ[𝓝 (0 : ℝ)]
      (fun t => (methodRun m (fun _ => Q t) (fun _ => Q t) g N).observationList.getD j 0) := by
    filter_upwards [hgood] with t ht
    have he := shadowSegments_methodRun m hm Q D g N t (B t) ht.1 ht.2.1 ht.2.2 N le_rfl
    exact congrArg (fun H : History E => H.observationList.getD j 0) he
  exact htransfer.trans hshadow.deriv_eq
end
end krylov.Envelope
