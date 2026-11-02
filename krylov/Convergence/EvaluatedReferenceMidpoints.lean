import krylov.Convergence.EvaluatedTensorCoordinates

/-!
Article: main_krylov, prop:EL, explicit evaluated-launch midpoint formula.
Use: derive both the interior two-trial formula and the terminal accumulated
miss formula from the actual quadratic evaluated-launch execution.
Source: true reference queries, evaluated displacement and full CG termination.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace BigOperators
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual physical reference miss for the evaluated-launch rule.
Article: main_krylov, prop:EL. -/
def evaluatedLaunchReferenceMiss (trial : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (i : ℕ) : E :=
  (CG.length Q g i-trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>Q) g i)) • CG.direction Q g i

/-- The genuine evaluated-launch reference step is the true CG line step
minus its actual trial miss. Article: prop:EL. -/
theorem evaluatedLaunchReferencePoint_step
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) (cgOperator base u) i)≠0) (i : ℕ) (hi : i<n) :
    oneGradientReferencePoint (evaluatedLaunchMethod trial) (cgOperator base) u (i+1)-
      oneGradientReferencePoint (evaluatedLaunchMethod trial) (cgOperator base) u i=
        referenceStep (cgOperator base) (cgOperator base u) i-
          evaluatedLaunchReferenceMiss trial (cgOperator base) (cgOperator base u) i := by
  rw [oneGradientReferencePoint_step,oneGradientStep,evaluated_launch_step trial (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 (cgOperator base u) n
    (fun j hj=>cg_nonstagnation base hb (cgOperator base u) j (by rw [hc];exact hj)) ht i hi.le]
  unfold referenceStep evaluatedLaunchReferenceMiss
  module

/-- Every real evaluated reference point retains the full sum of previous
trial misses. Article: main_krylov, prop:EL. -/
theorem evaluatedLaunchReferencePoint_eq_virtual_sub_sum
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) (cgOperator base u) i)≠0) (i : ℕ) (hi : i≤n) :
    oneGradientReferencePoint (evaluatedLaunchMethod trial) (cgOperator base) u i=
      fcQuadraticReferencePoint (cgOperator base) u i-
        ∑ j∈range i,evaluatedLaunchReferenceMiss trial (cgOperator base) (cgOperator base u) j := by
  rw [oneGradientReferencePoint,evaluated_launch_displacement trial (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 (cgOperator base u) n
    (fun j hj=>cg_nonstagnation base hb (cgOperator base u) j (by rw [hc];exact hj)) ht i hi]
  unfold fcQuadraticReferencePoint evaluatedLaunchReferenceMiss
  module

/-- The real compatible interior midpoint is exactly the source's
half sum of the two actual evaluated trial steps. Article: prop:EL. -/
theorem evaluatedLaunchReferenceMidpointDrift_interior
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) (cgOperator base u) i)≠0) (l : ℕ) (hl : l+1<n) :
    evaluatedLaunchReferenceMidpointDrift trial (cgOperator base) u l=
      (1/2:ℝ) • ((referenceStep (cgOperator base) (cgOperator base u) l-
          evaluatedLaunchReferenceMiss trial (cgOperator base) (cgOperator base u) l)+
        (referenceStep (cgOperator base) (cgOperator base u) (l+1)-
          evaluatedLaunchReferenceMiss trial (cgOperator base) (cgOperator base u) (l+1))) := by
  let p := oneGradientReferencePoint (evaluatedLaunchMethod trial) (cgOperator base) u
  have hmid : evaluatedLaunchReferenceMidpointDrift trial (cgOperator base) u l=
      (1/2:ℝ) • ((p (l+1)-p l)+(p (l+1+1)-p (l+1))) := by
    simp only [evaluatedLaunchReferenceMidpointDrift,oneGradientReferenceMidpoint,
      ite_eq_left hl,ite_eq_left (show l<n by omega)]
    change (1/2:ℝ) • (p (l+1)+p (l+1+1))-(1/2:ℝ) • (p l+p (l+1))=_
    module
  rw [hmid]
  dsimp only [p]
  rw [evaluatedLaunchReferencePoint_step trial base hb u hc ht l (by omega),
    evaluatedLaunchReferencePoint_step trial base hb u hc ht (l+1) hl]

/-- The terminal midpoint contains the true final CG step and all prior
misses, exactly as in the article's evaluated-launch formula. Article: prop:EL. -/
theorem evaluatedLaunchReferenceMidpointDrift_terminal
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) (cgOperator base u) i)) :
    evaluatedLaunchReferenceMidpointDrift trial (cgOperator base) u (n-1)=
      (1/2:ℝ) • (referenceStep (cgOperator base) (cgOperator base u) (n-1)+
        ∑ j∈range (n-1),evaluatedLaunchReferenceMiss trial (cgOperator base) (cgOperator base u) j) := by
  let m := evaluatedLaunchMethod trial
  let Q := cgOperator base
  have hzero := evaluatedLaunchReferenceOutput_zero trial base hb u hc ht
  have hvirt := (evaluated_launch_reference trial Q (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 (Q u) n
    (fun i hi=>cg_nonstagnation base hb (Q u) i (by rw [hc];exact hi))
    (fun i hi=>(ht i hi).ne') n le_rfl).1
  have hCG : fcQuadraticReferencePoint Q u n=0 := by
    have he : fcQuadraticReferencePoint Q u n=oneGradientReferenceOutput m Q u n := by
      unfold fcQuadraticReferencePoint oneGradientReferenceOutput oneGradientReferencePoint
      rw [←hvirt]
      unfold OneGradientMethod.outputDisplacement
      module
    rw [he]
    exact hzero
  have hstep := fcQuadraticReferencePoint_step Q u (n-1)
  rw [show n-1+1=n by omega,hCG] at hstep
  have hp : fcQuadraticReferencePoint Q u (n-1)= -referenceStep Q (Q u) (n-1) := by
    rw [←hstep]
    module
  simp only [evaluatedLaunchReferenceMidpointDrift,show n-1+1=n by omega,oneGradientReferenceMidpoint,
    ite_eq_right (show ¬n<n by omega),ite_eq_left (show n-1<n by omega),hzero]
  rw [evaluatedLaunchReferencePoint_eq_virtual_sub_sum trial base hb u hc
    (fun i hi=>(ht i hi).ne') (n-1) (by omega),hp]
  module

end
end krylov.Convergence
