import krylov.Envelope.CanonicalAbsorbedObservations
import krylov.Envelope.CanonicalAbsorbedSteps
import krylov.Envelope.ReferenceStepJet

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), complete actual source absorbed information fibre.
Use: identify every true observation and recorded-step first variation
on absorbed canonical scenarios with the exact printed affine quadratic
shadow, quantified over the genuine smooth source method class.
Source: actual primitive source-class membership, genuine full-history
positive quadratic shadow execution and true equal-operator-first-jet transfer.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability krylov.Secant krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- For every actual smooth globally CG-consistent source method, every genuine observed answer and history coordinate on a true absorbed canonical scenario has the exact first derivative of its literal affine single-quadratic transcript.
Use: For every actual smooth globally CG-consistent source method, every genuine observed answer and history coordinate on a true absorbed canonical scenario has the exact first derivative of its literal affine single-quadratic transcript.
Article: main_krylov, apB:lem:mu(c), complete actual source absorbed information fibre.
Proof: Derive genuine primitive smooth membership and actual activity from the real source class and active count. The actual canonical full-observation positive shadow first jet equals the true literal affine quadratic first jet. -/
theorem source_absorbed_observation_fibre (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (habs : AbsorbedIncrements base g E N)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) (j : ℕ) :
    deriv (fun t => (methodRun M.policy (canonicalFCPath base E t) (B t) g N).observationList.getD j 0) 0=
      deriv (fun t => (methodRun M.policy
        (fun _ => affineOracle (cgOperator base) (cgOperator (∑ l∈Finset.range (N-1),physicalIncrements base E l)) t)
        (fun _ => affineOracle (cgOperator base) (cgOperator (∑ l∈Finset.range (N-1),physicalIncrements base E l)) t)
        g N).observationList.getD j 0) 0 := by
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  have hs := M.smooth _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g N hpre
  have he := actual_absorbed_canonical_observation M.policy M.consistent base hb g N hcount hs E hE habs B hB0 hB j
  apply he.trans
  exact static_observation_affine_firstJet M.policy M.consistent _ _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g N hpre hs _ (positiveReferenceOperator_zero base _)
    (positiveReferenceOperator_hasDeriv base _) j

/-- For every actual smooth globally CG-consistent source method, every true recorded-step derivative on a genuine absorbed canonical scenario is exactly the actual CG step derivative for the printed affine quadratic perturbation.
Use: For every actual smooth globally CG-consistent source method, every true recorded-step derivative on a genuine absorbed canonical scenario is exactly the actual CG step derivative for the printed affine quadratic perturbation.
Article: main_krylov, apB:lem:mu(c), complete actual source absorbed information fibre.
Proof: Derive actual primitive cycle membership from the genuine source class. True absorbed recorded-step shadow transfer and actual CG operator-coordinate differentiability identify the real derivative with the literal affine quadratic CG step. -/
theorem source_absorbed_step_fibre (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (habs : AbsorbedIncrements base g E N)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0)
    (k : ℕ) (hk : k<N) :
    deriv (fun t => probedStep M.policy (canonicalFCPath base E t) (B t) g k) 0=
      deriv (fun t => referenceStep
        (affineOracle (cgOperator base) (cgOperator (∑ l∈Finset.range (N-1),physicalIncrements base E l)) t) g k) 0 := by
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  have hs := M.smooth _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g N hpre
  have he := actual_absorbed_canonical_step M.policy M.consistent base hb g N hcount hs E hE habs B hB0 hB k hk
  apply he.trans
  exact referenceStep_affine_firstJet _ _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g k
    (fun i hi => hpre i (hi.trans_lt hk)) _ (positiveReferenceOperator_zero base _) (positiveReferenceOperator_hasDeriv base _)
end
end krylov.Envelope
