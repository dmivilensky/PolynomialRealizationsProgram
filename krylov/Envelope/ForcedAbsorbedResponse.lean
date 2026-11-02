import krylov.Envelope.CanonicalShadow
import krylov.Envelope.TiltAbsorption

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(c), true class-quantified forced absorbed response.
Use: prove every actual member of the genuine smooth CG-consistent source
class has the same real minus-tilt first variation on the actual
budget-preserving absorbed scenario, for the original source increments.
Source: constructed true positive quadratic information fibre, actual
primitive class membership and genuine absorbed invariance of the common tilt.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual genuine smooth globally CG-consistent source-class member has forced transverse first variation equal to minus the original true common tilt on the actual absorbed canonical scenario.
Use: Every actual genuine smooth globally CG-consistent source-class member has forced transverse first variation equal to minus the original true common tilt on the actual absorbed canonical scenario.
Article: main_krylov, thm:select and apB:lem:mu(c), true class-quantified forced absorbed response.
Proof: Derive the real primitive smooth representation from genuine class membership. Apply the actual absorbed quadratic-shadow response to true symmetric compressed increments and identify their genuine invariant common tilt with that of the original source scenario. -/
theorem forced_absorbed_response (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) :
    (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹
      (deriv (fun t => probedGradient M.policy (canonicalFCPath base (absorbedIncrements base g E) t) (B t) g N) 0))=
        -commonTilt base g (canonicalFCPath base E) N := by
  have hs := M.smooth (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))
  rw [actual_absorbed_transverse M.policy M.consistent base hb g N hN hcount hs
    (absorbedIncrements base g E) (fun l hl => absorbedIncrements_symm base g E l (hE l hl))
    (absorbedIncrements_absorbed base g E N) B hB0 hB,commonTilt_absorbedIncrements base hb g N hcount E]
end
end krylov.Envelope
