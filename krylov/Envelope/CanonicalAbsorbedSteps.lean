import krylov.Envelope.PhysicalAbsorbedSteps
import krylov.Envelope.CanonicalShadow

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual canonical absorbed recorded-step fibre.
Use: derive the true method-independent CG recorded-step first variation
on every genuine absorbed canonical source scenario.
Source: actual canonical-to-physical increment geometry, genuine active
reference domains and the real positive quadratic recorded-step shadow.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability krylov.Secant krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every genuine recorded-step first derivative of an actual smooth globally CG-consistent method on a real absorbed canonical scenario equals the true positive single-quadratic CG step derivative.
Use: Every genuine recorded-step first derivative of an actual smooth globally CG-consistent method on a real absorbed canonical scenario equals the true positive single-quadratic CG step derivative.
Article: main_krylov, apB:lem:mu(c), actual canonical absorbed recorded-step fibre.
Proof: Derive actual reference activity, true physical increment symmetry and old-gradient annihilation from genuine canonical absorption; apply the proved real physical recorded-step information fibre. -/
theorem actual_absorbed_canonical_step
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (habs : AbsorbedIncrements base g E N)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) (k : ℕ) (hk : k<N) :
    deriv (fun t => probedStep m (canonicalFCPath base E t) (B t) g k) 0=
      deriv (fun t => referenceStep
        (positiveReferenceOperator base (∑ l∈Finset.range (N-1),physicalIncrements base E l) t) g k) 0 := by
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (hi.trans_le hcount)
  have he := actual_absorbed_physical_step m hm base hb g N hpre hsmooth (physicalIncrements base E)
    (fun l hl => physicalIncrements_symm base E l (hE l hl))
    (physicalIncrements_kill_gradients base hb g E N hpre habs) B hB0 hB k hk
  rwa [canonicalFCPath_eq_cumulative] at he

end
end krylov.Envelope
