import krylov.Envelope.AbsorbedShadow
import krylov.Envelope.FiniteStepJets

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual recorded steps on the absorbed information fibre.
Use: identify every genuine recorded-step first variation on actual
absorbed operator increments with the true CG step derivative on one
positive quadratic shadow, independently of the executed method.
Source: actual finite recorded-step oracle charts, genuine moving-shadow
whole-history equality and real exact-search CG scale cancellation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability Filter Topology
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every actual recorded step before the genuine active horizon has the true CG step derivative on the single-quadratic shadow for real symmetric absorbed increments.
Use: Every actual recorded step before the genuine active horizon has the true CG step derivative on the single-quadratic shadow for real symmetric absorbed increments.
Article: main_krylov, apB:lem:mu(c), actual recorded steps on the absorbed information fibre.
Proof: Transfer the genuine recorded-step first jet through the actual moving shadow with matching real operator first jets. Exact true shadow histories and genuine quadratic scale cancellation identify the real static recorded step with its actual CG step. -/
theorem actual_absorbed_shadow_step (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : ℝ → E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hQ : (Q 0).toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q 0 v))
    (hpre : ∀ i<N, CG.gradient (Q 0) g i≠0) (hsmooth : SmoothProbedCycleAt m 2 (Q 0) g N)
    (haQ : AnalyticAt ℝ Q 0) (hdQ : HasDerivAt Q (∑ l∈Finset.range (N-1),D l) 0)
    (hgood : ∀ᶠ t in 𝓝 (0 : ℝ), (Q t).toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q t v)) ∧ ∀ i<N, CG.gradient (Q t) g i≠0)
    (hD : ∀ l<N-1, (D l).toLinearMap.IsSymmetric)
    (hkill : ∀ l<N-1, ∀ i≤l, D l (CG.gradient (Q 0) g i)=0)
    (B : ℝ → ℕ → E →L[ℝ] E) (hB0 : B 0=fun _ => Q 0)
    (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) (k : ℕ) (hk : k<N) :
    deriv (fun t => probedStep m (cumulativeOraclePath (Q 0) D t) (B t) g k) 0=
      deriv (fun t => referenceStep (Q t) g k) 0 := by
  -- True moving CG regularity derives the actual absorbed operator first jets before transferring the genuine recorded-step derivative.
  have hG (i : ℕ) (hi : i<N) : ContDiffAt ℝ 2 (fun t => CG.gradient (Q t) g i) 0 :=
    (cg_prefix_analytic Q (fun _ => g) 0 haQ analyticAt_const hQ hpos i (fun j hj => hpre j (hj.trans hi))).1.contDiffAt
  have hS0 : shadowSegments Q D g N 0=fun _ => Q 0 := funext (fun k => shadowSegments_zero Q D g N k)
  have htransfer := actual_step_firstJet_transfer m hm (Q 0) hQ hpos g N hpre hsmooth
    (cumulativeOraclePath (Q 0) D) B (shadowSegments Q D g N) B
    (fun k => ∑ l∈Finset.range k,D l) (fun k => deriv (fun t => B t k) 0)
    (cumulativeOraclePath_zero (Q 0) D) hB0 hS0 hB0
    (fun i _ => cumulativeOraclePath_hasDeriv (Q 0) D i) (fun i hi => (hB i hi).hasDerivAt)
    (fun i hi => shadowSegments_hasDeriv Q D g N i hi hdQ hG hpre hD hkill) (fun i hi => (hB i hi).hasDerivAt) k hk
  -- Exact genuine shorter shadow histories identify the actual recorded step with the true single-quadratic CG step, cancelling every real positive direction scale.
  have hshadow : (fun t => probedStep m (shadowSegments Q D g N t) (B t) g k)=ᶠ[𝓝 (0 : ℝ)]
      (fun t => referenceStep (Q t) g k) := by
    filter_upwards [hgood] with t ht
    have he := shadowSegments_methodRun m hm Q D g N t (B t) ht.1 ht.2.1 ht.2.2 (k+1) hk
    exact (congrArg (fun H : History E => H.observationList.getD 4 0) he).trans
      (quadratic_probedStep_eq_cg m hm (Q t) ht.1 ht.2.1 g k)
  exact htransfer.trans hshadow.deriv_eq
end
end krylov.Envelope
