import krylov.Correction.RFCInitialReference
import krylov.Correction.IncomingResidual
import krylov.Stability.CanonicalDirectionGeometry

/-!
Article: main_krylov, thm:UCq, true small intermediate RFC search.
Use: Derive the genuine second searched-line error relative to its own CG
step norm, with no nonstagnation cutoff or minimum intermediate energy.
Source: proved exact original first history and second CG direction, true
canonical search covariance and actual positive reciprocal-curvature bounds.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- With its original unchanged first base probe, the actual second ordinary-RFC line is nonzero and differs from CG by at most twice the canonical operator budget times that genuine CG step norm.
Use: Supply the true arbitrarily small intermediate-line mechanism in the three-dimensional uniform exception.
Article: main_krylov, thm:UCq.
Proof: Exact complete first-history equality gives the true CG gradient and direction at the second search. Genuine metric-root pairing identifies both actual line formulas. Apply the proved relative reference-line estimate and positive-curvature nonzeroness, preserving the real reference step norm rather than replacing it by a larger gradient bound.
-/
theorem ordinary_second_line_relative (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (hA0 : A 0=cgOperator base)
    (hpre : ∀ i≤1, CG.gradient (cgOperator base) g i≠0)
    {ε : ℝ} (hA1 : ‖canonicalOperator base (A 1)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hε : ε≤1/2) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    ‖R (fullLineStep 1 A B g 1)-canonicalCGStep base g 1‖≤2*ε*‖canonicalCGStep base g 1‖ ∧
      R (fullLineStep 1 A B g 1)≠0 := by
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let D := R (CG.direction (cgOperator base) g 1)
  have hp := cgOperator_positive base hb
  have hh := ordinary_initial_history A B (cgOperator base) g hA0
  have hg : (methodRun m A B g 1).gradient=CG.gradient (cgOperator base) g 1 :=
    (congrArg History.gradient hh).trans
      (rfcMethod_static fullMemory 1 (cgOperator base) hp.1 hp.2 g (fun _ _ hj => hj) 1).1
  have hd : m.direction (methodRun m A B g 1)=CG.direction (cgOperator base) g 1 :=
    ordinary_second_direction A B (cgOperator base) hp.1 hp.2 g hA0
  have hDn : D≠0 := canonicalCG_direction_ne base hb g 1 hpre
  have hreference : lineLength (cgCanonicalError base g 1) D D • D=canonicalCGStep base g 1 :=
    canonicalCG_line_step base hb g 1
  have hactual : R (fullLineStep 1 A B g 1)=
      lineLength (cgCanonicalError base g 1) D (canonicalOperator base (A 1) D) • D := by
    unfold fullLineStep
    dsimp only
    rw [hd,hg,map_smul]
    dsimp only [D,cgCanonicalError,R]
    rw [canonicalOperator_primal base hb,canonical_lineLength base hb]
  have hbound := lineStep_reference_relative (canonicalOperator base (A 1))
    (cgCanonicalError base g 1) D hDn hA1 hε
  rw [hreference,← hactual] at hbound
  have hnonzero := lineStep_reference_nonzero (canonicalOperator base (A 1))
    (cgCanonicalError base g 1) D hDn hA1 hε
    (by rw [hreference]; exact canonicalCGStep_ne_zero base hb g 1 hpre)
  rw [← hactual] at hnonzero
  exact ⟨hbound,hnonzero⟩

end
end krylov.Correction
