import krylov.Stability.RFCSProjectedOrders
import krylov.Correction.IncomingResidual

/-!
Article: main_krylov, thm:RFCS, genuine only-last-probe first-order expansion.
Use: the actual independently probed RFC-S executor has only its final
probe mismatch in the true first variation, with a derived quadratic remainder.
Source: actual analytic measured histories, the genuine predicted-model
projected residual, full reference rank and exact physical mismatch balance.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual RFC-S predicted line displacement is analytic and has precisely the genuine original CG reference step.
Use: replacing the final actual line by its true reference costs one order against the original small probe mismatch.
Article: main_krylov, thm:RFCS, actual line-step first-order replacement.
Proof: actual prefix analyticity supplies the genuine gradient and raw
direction. Real quadratic CG positivity makes the actual probe curvature
nonzero at the reference. Analytic division gives the true line step and
exact reference execution identifies its value with the original CG step. -/
theorem rfcSLineStep_regular (memory : ℕ → ℕ)
    (Ap A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hAp : ∀ i, AnalyticAt ℝ (fun z => Ap z i) 0)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0)
    (hg : AnalyticAt ℝ g 0) (Q : E →L[ℝ] E)
    (hAp0 : Ap 0=(fun _ => Q)) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g 0) k≠0 → 0<k → 0<memory k)
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    AnalyticAt ℝ (fun z => rfcSLineStep memory (Ap z) (A z) (B z) (g z) k) 0 ∧
      rfcSLineStep memory (Ap 0) (A 0) (B 0) (g 0) k=referenceStep Q (g 0) k := by
  -- The true current reference curvature justifies the actual independently probed search quotient.
  have ht := quadraticRFCS_prefix_analytic memory Ap A B g 0 hAp hA hB hg Q hAp0 hA0 hB0 hQ hpos hm
    (k+1) (fun i hi => hpre i (by omega))
  have hG := (quadraticRFCS_prefix_analytic memory Ap A B g 0 hAp hA hB hg Q hAp0 hA0 hB0 hQ hpos hm
    k (fun i hi => hpre i hi.le)).1
  let d := fun z => rfcSDirection memory (Ap z) (A z) (B z) (g z) k
  let z := fun p => Ap p k (d p)
  have hD : AnalyticAt ℝ d 0 := (ht.2 k (Nat.lt_succ_self k)).1
  have hZ : AnalyticAt ℝ z 0 := analytic_operator_apply (hAp k) hD
  have hD0 : d 0=CG.direction Q (g 0) k := by
    dsimp only [d]
    rw [hAp0,hA0,hB0,(rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) k).2.1]
    exact rfc_reference_direction memory 1 Q hQ hpos (g 0) hm k
  have hG0 : rfcSGradient memory (Ap 0) (A 0) (B 0) (g 0) k=CG.gradient Q (g 0) k := by
    rw [hAp0,hA0,hB0,(rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) k).1]
    exact (rfcMethod_static memory 1 Q hQ hpos (g 0) hm k).1
  have hZ0 : z 0=Q (CG.direction Q (g 0) k) := by dsimp only [z]; rw [hAp0,hD0]
  have hcurv : inner ℝ (d 0) (z 0)≠0 := by
    rw [hD0,hZ0]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g 0) k
      (CG.invariant Q hQ hpos (g 0) k (fun i hi => hpre i hi.le)) (hpre k le_rfl)).1).ne'
  refine ⟨((analytic_inner hD hG).neg.div (analytic_inner hD hZ) hcurv).smul hD,?_⟩
  change lineLength (rfcSGradient memory (Ap 0) (A 0) (B 0) (g 0) k) (d 0) (z 0) • d 0=_
  rw [hG0,hD0,hZ0]
  rfl

end
end krylov.Correction

