import krylov.Stability.ActualObservedSearch
import krylov.Correction.ChronologicalCorrection

/-!
Article: main_krylov, thm:UCq, true ordinary last-search comparison.
Use: Apply the established uniform observed-search estimate to the genuine
ordinary executor through its proved complete accepted-prefix equality.
Source: the existing actual gated observed-search estimate and exact full
history, real recorded-step and observed-gradient coordinate identities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true ordinary-RFC searched line has the original uniform CG comparison whenever its genuine earlier observed bounds and exact accepted shadow prefix hold.
Use: Control the actual last searched displacement without a lower bound on its reference energy or its true line length.
Article: main_krylov, thm:UCq.
Proof: Complete true prefix equality identifies actual old recorded steps, measured secants, current direction and real searched line. Apply the existing actual observed-search theorem to that same run and transfer its genuine line estimate back exactly.
-/
theorem ordinary_observed_next_line_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) {μ κ C a K ε : ℝ}
    (hμ : 0<μ) (hκ : 1≤κ) (hC : 0≤C) (ha : 0≤a) (hK : 0≤K)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (hε : 0≤ε) (hεone : ε≤1) (hhalf : ε≤1/2)
    (hGramSmall : a*ε≤1/2) (hSolve : a*ε+(k : ℝ)*(K*ε)≤1/2)
    (hProj : 4*Real.sqrt k*(K*ε)≤1/2)
    (heq : ∀ j≤k, methodRun (gatedMethod fullMemory (1/2)) A B g j=
      methodRun (rfcMethod fullMemory 1) A B g j) :
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
    let R := cgOperator (metricRoot base)
    let J := cgOperator (metricRoot base)⁻¹
    (∀ i<k, R (probedStep m A B g i)≠0) →
    (∀ i<k, ‖J (probedSecant m A B g i)-R (probedStep m A B g i)‖≤K*ε*‖R (probedStep m A B g i)‖) →
    ‖crossGram (unitWindow (fun i : Fin k => R (probedStep m A B g i.val)))
      (unitWindow (fun i : Fin k => R (probedStep m A B g i.val)))-1‖≤a*ε →
    R (m.direction (methodRun m A B g k))≠0 →
    ‖canonicalOperator base (A k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε →
    (∀ i<k, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤C*ε) →
    ‖R (fullLineStep 1 A B g k)-canonicalCGStep base g k‖≤
      observedCGStepConstant k κ C ((k : ℝ)*(C+K*(C+1))) a K*ε := by
  dsimp only
  intro hs hy hGram hd hA hstep
  let mg := gatedMethod fullMemory (1/2) (E := EuclideanSpace ℝ (Fin n))
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let R := cgOperator (metricRoot base)
  have hgrad j (hj : j≤k) : probedGradient mg A B g j=probedGradient m A B g j :=
    congrArg History.gradient (heq j hj)
  have hsteps j (hj : j<k) : probedStep mg A B g j=probedStep m A B g j :=
    congrArg (fun H : History (EuclideanSpace ℝ (Fin n)) => H.observationList.getD 4 0)
      (heq (j+1) (by omega))
  have hsecants j (hj : j<k) : probedSecant mg A B g j=probedSecant m A B g j := by
    rw [probedSecant,probedSecant,hgrad (j+1) (by omega),hgrad j hj.le]
  have hdir : mg.direction (methodRun mg A B g k)=m.direction (methodRun m A B g k) := by
    change windowDirection (selectedWindow fullMemory (methodRun mg A B g k)) _=_
    rw [heq k le_rfl]
    rfl
  have hS : (fun i : Fin k => R (probedStep mg A B g i.val))=
      fun i => R (probedStep m A B g i.val) := by
    funext i; rw [hsteps i.val i.isLt]
  have ht := gated_observed_next_line_bound base hb (1/2) A B g k
    hμ hκ hC ha hK hspec hinit hpre hε hεone hhalf hGramSmall hSolve hProj
    (fun i hi => by rw [hsteps i hi]; exact hs i hi)
    (fun i hi => by rw [hsecants i hi,hsteps i hi]; exact hy i hi)
    (by change ‖crossGram (unitWindow (fun i : Fin k => R (probedStep mg A B g i.val)))
          (unitWindow (fun i : Fin k => R (probedStep mg A B g i.val)))-1‖≤a*ε
        rw [hS]; exact hGram)
    (by rw [hdir]; exact hd) hA
    (fun i hi => by rw [hsteps i hi]; exact hstep i hi)
  have hline : gatedObservedLineStep (1/2) A B g k=fullLineStep 1 A B g k := by
    unfold gatedObservedLineStep fullLineStep
    dsimp only
    rw [heq k le_rfl]
    rfl
  rw [hline] at ht
  exact ht

end
end krylov.Correction
