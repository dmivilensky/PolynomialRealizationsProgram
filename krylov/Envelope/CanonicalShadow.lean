import krylov.Envelope.CanonicalAbsorption
import krylov.Envelope.PhysicalAbsorbedShadow
import krylov.Envelope.RealizationDifference

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c) and thm:select, genuine canonical absorbed information fibre.
Use: identify actual smooth globally CG-consistent method gradients on
true absorbed canonical scenarios with a real single-quadratic CG shadow,
and derive the genuine forced minus-tilt transverse response and zero residual.
Source: actual canonical/physical increment equality, constructed positive
quadratic shadow, genuine global CG consistency and true RFC coefficient membership.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability krylov.Secant krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual canonical source path is exactly the genuine cumulative physical increment operator path.
Use: The actual canonical source path is exactly the genuine cumulative physical increment operator path.
Article: main_krylov, apB:lem:mu(c) and thm:select, genuine canonical absorbed information fibre.
Proof: Distribute the true positive-root congruence through the actual finite canonical increment prefix. -/
theorem canonicalFCPath_eq_cumulative (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    cumulativeOraclePath (cgOperator base) (fun l => cgOperator (physicalIncrements base E l))=canonicalFCPath base E := by
  funext t k
  rw [cumulativeOraclePath,canonicalFCPath,cumulative_physicalIncrements]

/-- Every actual smooth globally CG-consistent method has the true explicitly constructed single-quadratic CG gradient derivative on genuine absorbed canonical scenarios.
Use: Every actual smooth globally CG-consistent method has the true explicitly constructed single-quadratic CG gradient derivative on genuine absorbed canonical scenarios.
Article: main_krylov, apB:lem:mu(c) and thm:select, genuine canonical absorbed information fibre.
Proof: Actual active count gives the true nonstagnating CG prefix. Canonical absorption derives real physical increment symmetry and old-gradient annihilation; the genuine positive quadratic shadow theorem then identifies the actual gradient derivative. -/
theorem actual_absorbed_canonical_gradient
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (habs : AbsorbedIncrements base g E N)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) :
    deriv (fun t => probedGradient m (canonicalFCPath base E t) (B t) g N) 0=
      deriv (fun t => CG.gradient
        (positiveReferenceOperator base (∑ l∈Finset.range (N-1),physicalIncrements base E l) t) g N) 0 := by
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (hi.trans_le hcount)
  have he := actual_absorbed_physical_gradient m hm base hb g N hpre hsmooth (physicalIncrements base E)
    (fun l hl => physicalIncrements_symm base E l (hE l hl))
    (physicalIncrements_kill_gradients base hb g E N hpre habs) B hB0 hB
  rwa [canonicalFCPath_eq_cumulative] at he

/-- Every actual primitive smooth globally CG-consistent method has genuinely forced transverse variation equal to minus the true common tilt on real absorbed canonical scenarios.
Use: Every actual primitive smooth globally CG-consistent method has genuinely forced transverse variation equal to minus the true common tilt on real absorbed canonical scenarios.
Article: main_krylov, apB:lem:mu(c) and thm:select, genuine canonical absorbed information fibre.
Proof: Both the actual method and genuine full-memory RFC have the same real single-quadratic shadow gradient derivative. True RFC primitive smooth membership is derived from its actual coefficients, and its genuine residual-order theorem gives the real minus-tilt response. -/
theorem actual_absorbed_transverse
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (habs : AbsorbedIncrements base g E N)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) :
    (exploredFlag base g N).starProjection
      (cgOperator (metricRoot base)⁻¹ (deriv (fun t => probedGradient m (canonicalFCPath base E t) (B t) g N) 0))=
      -commonTilt base g (canonicalFCPath base E) N := by
  -- Compare genuine raw-method and actual RFC derivatives on the same true positive quadratic shadow; RFC membership and its real residual cancellation are proved inputs.
  let A := canonicalFCPath base E
  have hr := rfcMethod_consistent fullMemory (fun _ hk => hk) 1 (E := EuclideanSpace ℝ (Fin n))
  have hs := rfcMethod_smoothCycleAt fullMemory 1 (cgOperator base) (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g (fun _ _ hk => hk) N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount)) 2
  have hmjet := actual_absorbed_canonical_gradient m hm base hb g N hcount hsmooth E hE habs B hB0 hB
  have hrjet := actual_absorbed_canonical_gradient (rfcMethod fullMemory 1) hr base hb g N hcount hs E hE habs A
    (canonicalFCPath_zero base E) (fun i _ => (canonicalFCPath_calculus base E i).1.differentiableAt)
  have he : deriv (fun t => probedGradient m (A t) (B t) g N) 0=
      deriv (fun t => probedGradient (rfcMethod fullMemory 1) (A t) (A t) g N) 0 := hmjet.trans hrjet.symm
  change (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹
    (deriv (fun t => probedGradient m (A t) (B t) g N) 0))=_
  rw [he]
  exact fullRFC_tilt 1 (by norm_num) base hb g A A (fun i => (canonicalFCPath_calculus base E i).1)
    (fun i => (canonicalFCPath_calculus base E i).1) (canonicalFCPath_zero base E) (canonicalFCPath_zero base E) N hN hcount

/-- Every actual smooth source-admissible globally CG-consistent method has exactly zero genuine observed residual variation on true absorbed canonical scenarios.
Use: Every actual smooth source-admissible globally CG-consistent method has exactly zero genuine observed residual variation on true absorbed canonical scenarios.
Article: main_krylov, apB:lem:mu(c) and thm:select, genuine canonical absorbed information fibre.
Proof: Combine the real forced absorbed minus-tilt transverse response with the proved genuine actual residual/tilt splitting. -/
theorem actual_absorbed_residualVariation_zero (memory : ℕ → ℕ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (habs : AbsorbedIncrements base g E N)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0) :
    residualVariation base g m (canonicalFCPath base E) B N=0 := by
  have ht := actual_tilt_splitting memory m hm hspan (canonicalFCPath base E) B g base hb
    (canonicalFCPath_zero base E) hB0 N (fun i _ => (canonicalFCPath_calculus base E i).1.contDiffAt) hB hcount hsmooth
  change (exploredFlag base g N).starProjection
    (cgOperator (metricRoot base)⁻¹ (deriv (fun t => probedGradient m (canonicalFCPath base E t) (B t) g N) 0))=_ at ht
  rw [actual_absorbed_transverse m hm base hb g N hN hcount hsmooth E hE habs B hB0
    (fun i hi => (hB i hi).differentiableAt (by norm_num))] at ht
  have he := congrArg (fun v => v+commonTilt base g (canonicalFCPath base E) N) ht
  simpa only [neg_add_cancel,sub_add_cancel] using he.symm
end
end krylov.Envelope
