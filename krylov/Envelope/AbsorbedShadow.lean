import krylov.Envelope.ShadowSegments
import krylov.Envelope.OracleFirstJets
import krylov.Stability.AnalyticCG

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual absorbed information-fibre first derivatives.
Use: prove genuine smooth globally CG-consistent raw-method gradients have
the actual single-quadratic CG first derivative on true absorbed changing
operator paths, including arbitrary genuine smooth correction paths.
Source: exact real moving quadratic shadow execution, true absorbed
operator first jets and actual finite oracle-coordinate chain rules.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability Filter Topology
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual affine physical operator path with genuine cumulative segment increments.
Use: The actual affine physical operator path with genuine cumulative segment increments.
Article: main_krylov, apB:lem:mu(c), actual absorbed information-fibre first derivatives.
Proof: Add the real finite increment prefix to the actual reference operator. -/
def cumulativeOraclePath (Q : E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (t : ℝ) (k : ℕ) : E →L[ℝ] E :=
  Q+t • ∑ l∈Finset.range k,D l

omit [CompleteSpace E] in
/-- The actual cumulative physical perturbation path starts at the genuine constant reference.
Use: The actual cumulative physical perturbation path starts at the genuine constant reference.
Article: main_krylov, apB:lem:mu(c), actual absorbed information-fibre first derivatives.
Proof: The true affine perturbation multiplier vanishes at zero. -/
theorem cumulativeOraclePath_zero (Q : E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) :
    cumulativeOraclePath Q D 0=fun _ => Q := by
  funext k
  simp only [cumulativeOraclePath,zero_smul,add_zero]

omit [CompleteSpace E] in
/-- Every actual cumulative physical segment has exactly its genuine finite increment-prefix derivative.
Use: Every actual cumulative physical segment has exactly its genuine finite increment-prefix derivative.
Article: main_krylov, apB:lem:mu(c), actual absorbed information-fibre first derivatives.
Proof: Differentiate the true constant plus the real parameter times its actual finite increment sum. -/
theorem cumulativeOraclePath_hasDeriv (Q : E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (k : ℕ) :
    HasDerivAt (fun t => cumulativeOraclePath Q D t k) (∑ l∈Finset.range k,D l) 0 := by
  convert! (hasDerivAt_const (0 : ℝ) Q).add ((hasDerivAt_id (0 : ℝ)).smul_const (∑ l∈Finset.range k,D l)) using 1
  simp only [zero_add,one_smul]

/-- Every actual primitive smooth globally CG-consistent method has exactly the genuine single-quadratic shadow CG gradient derivative on real symmetric absorbed cumulative physical increments.
Use: Every actual primitive smooth globally CG-consistent method has exactly the genuine single-quadratic shadow CG gradient derivative on real symmetric absorbed cumulative physical increments.
Article: main_krylov, apB:lem:mu(c), actual absorbed information-fibre first derivatives.
Proof: Derive actual moving-compression smoothness from the true analytic CG reference. The real moving shadow shares exactly the genuine cumulative operator first jets, so actual finite-oracle differentiation transfers the true method derivative. Genuine global CG consistency identifies its exact nearby complete shadow execution with actual CG on one positive quadratic. -/
theorem actual_absorbed_shadow_gradient (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : ℝ → E →L[ℝ] E) (D : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hQ : (Q 0).toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q 0 v))
    (hpre : ∀ i<N, CG.gradient (Q 0) g i≠0) (hsmooth : SmoothProbedCycleAt m 2 (Q 0) g N)
    (haQ : AnalyticAt ℝ Q 0) (hdQ : HasDerivAt Q (∑ l∈Finset.range (N-1),D l) 0)
    (hgood : ∀ᶠ t in 𝓝 (0 : ℝ), (Q t).toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q t v)) ∧ ∀ i<N, CG.gradient (Q t) g i≠0)
    (hD : ∀ l<N-1, (D l).toLinearMap.IsSymmetric)
    (hkill : ∀ l<N-1, ∀ i≤l, D l (CG.gradient (Q 0) g i)=0)
    (B : ℝ → ℕ → E →L[ℝ] E) (hB0 : B 0=fun _ => Q 0)
    (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) :
    deriv (fun t => probedGradient m (cumulativeOraclePath (Q 0) D t) (B t) g N) 0=
      deriv (fun t => CG.gradient (Q t) g N) 0 := by
  -- Derive actual moving CG regularity before constructing the genuine absorbed shadow first jets.
  have hG (i : ℕ) (hi : i<N) : ContDiffAt ℝ 2 (fun t => CG.gradient (Q t) g i) 0 :=
    (cg_prefix_analytic Q (fun _ => g) 0 haQ analyticAt_const hQ hpos i (fun j hj => hpre j (hj.trans hi))).1.contDiffAt
  have hS0 : shadowSegments Q D g N 0=fun _ => Q 0 := funext (fun k => shadowSegments_zero Q D g N k)
  have htransfer := actual_gradient_firstJet_transfer m hm (Q 0) hQ hpos g N hpre hsmooth
    (cumulativeOraclePath (Q 0) D) B (shadowSegments Q D g N) B
    (fun k => ∑ l∈Finset.range k,D l) (fun k => deriv (fun t => B t k) 0)
    (cumulativeOraclePath_zero (Q 0) D) hB0 hS0 hB0
    (fun i _ => cumulativeOraclePath_hasDeriv (Q 0) D i) (fun i hi => (hB i hi).hasDerivAt)
    (fun i hi => shadowSegments_hasDeriv Q D g N i hi hdQ hG hpre hD hkill) (fun i hi => (hB i hi).hasDerivAt)
  -- On the true active positive neighborhood, all genuine oracle answers and complete histories coincide exactly with the actual single-quadratic execution.
  have hshadow : (fun t => probedGradient m (shadowSegments Q D g N t) (B t) g N)=ᶠ[𝓝 (0 : ℝ)]
      (fun t => CG.gradient (Q t) g N) := by
    filter_upwards [hgood] with t ht
    have he := shadowSegments_methodRun m hm Q D g N t (B t) ht.1 ht.2.1 ht.2.2 N le_rfl
    exact (congrArg History.gradient he).trans (quadratic_gradient_eq_cg m hm (Q t) ht.1 ht.2.1 g N)
  exact htransfer.trans hshadow.deriv_eq
end
end krylov.Envelope
