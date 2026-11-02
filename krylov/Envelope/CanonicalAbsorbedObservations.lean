import krylov.Envelope.PhysicalAbsorbedObservations
import krylov.Envelope.CanonicalShadow

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), true full observed canonical absorbed fibre.
Use: prove every actual observation coordinate on a genuine absorbed
canonical scenario has the exact true first derivative of its real
positive single-quadratic CG-consistent transcript.
Source: actual canonical/physical increment identification, genuine
absorption geometry and the proved positive full-observation information shadow.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability krylov.Secant krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual full-history observation coordinate on a genuine symmetric absorbed canonical scenario has exactly the true first derivative of its constructed positive single-quadratic transcript.
Use: Every actual full-history observation coordinate on a genuine symmetric absorbed canonical scenario has exactly the true first derivative of its constructed positive single-quadratic transcript.
Article: main_krylov, apB:lem:mu(c), true full observed canonical absorbed fibre.
Proof: Derive real reference activity from the genuine active count, transfer actual canonical absorption to true symmetric physical old-gradient-annihilating increments, and apply the real full-observation positive shadow theorem. -/
theorem actual_absorbed_canonical_observation
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N≤referenceAtomCount base hb g) (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (habs : AbsorbedIncrements base g E N)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) (j : ℕ) :
    deriv (fun t => (methodRun m (canonicalFCPath base E t) (B t) g N).observationList.getD j 0) 0=
      deriv (fun t => (methodRun m
        (fun _ => positiveReferenceOperator base (∑ l∈Finset.range (N-1),physicalIncrements base E l) t)
        (fun _ => positiveReferenceOperator base (∑ l∈Finset.range (N-1),physicalIncrements base E l) t) g N).observationList.getD j 0) 0 := by
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (hi.trans_le hcount)
  have he := actual_absorbed_physical_observation m hm base hb g N hpre hsmooth (physicalIncrements base E)
    (fun l hl => physicalIncrements_symm base E l (hE l hl))
    (physicalIncrements_kill_gradients base hb g E N hpre habs) B hB0 hB j
  rwa [canonicalFCPath_eq_cumulative] at he

end
end krylov.Envelope
