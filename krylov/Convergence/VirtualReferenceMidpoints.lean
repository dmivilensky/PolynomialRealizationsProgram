import krylov.Convergence.VirtualTensorCoordinates

/-!
Article: main_krylov, thm:V, explicit compatible midpoint geometry.
Use: derive the original three-step midpoint formula from the actual
quadratic XRFC trajectory. Missed components are the real trial errors,
and the terminal formula uses the true unevaluated quadratic minimizer.
Source: genuine virtual/evaluated CG identities and elementary affine algebra.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The true missed reference line component, without dividing by a
possibly zero line length outside the active prefix. Article: thm:V. -/
def xrfcReferenceMiss (trial : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (i : ℕ) : E :=
  (CG.length Q g i-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>Q) g i)) • CG.direction Q g i

/-- The absent previous miss at the initial point is exactly zero.
Article: thm:V, the sigma_{-1}=0 endpoint convention. -/
def xrfcPreviousMiss (trial : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (i : ℕ) : E :=
  if i=0 then 0 else xrfcReferenceMiss trial Q g (i-1)

/-- Every actual evaluated quadratic vertex is its true virtual CG point
minus the preceding missed line component. Article: main_krylov, thm:V. -/
theorem xrfcReferencePoint_eq_virtual_sub_miss
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i)≠0) (i : ℕ) (hi : i≤n) :
    oneGradientReferencePoint (xrfcMethod fullMemory trial) (cgOperator base) u i=
      fcQuadraticReferencePoint (cgOperator base) u i-
        xrfcPreviousMiss trial (cgOperator base) (cgOperator base u) i := by
  cases i with
  | zero=>simp [oneGradientReferencePoint,fcQuadraticReferencePoint,xrfcPreviousMiss,
      oneGradientRun,History.displacement,CG.displacement]
  | succ j=>
    have he := xrfc_full_evaluated trial (cgOperator base) (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 (cgOperator base u) n
      (fun a ha=>cg_nonstagnation base hb (cgOperator base u) a (by rw [hc];exact ha)) ht j (by omega)
    rw [oneGradientReferencePoint,he,fcQuadraticReferencePoint,CG.displacement_succ]
    simp only [xrfcPreviousMiss,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,
      Nat.add_sub_cancel,xrfcReferenceMiss]
    module

/-- Every nonterminal true compatible midpoint difference is the source
three-step expression, with the original previous and next trial misses.
Article: main_krylov, thm:V, explicit xi_l for l<n-1. -/
theorem xrfcReferenceMidpointDrift_interior
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i)≠0) (l : ℕ) (hl : l+1<n) :
    xrfcReferenceMidpointDrift trial (cgOperator base) u l=
      (1/2:ℝ) • (xrfcPreviousMiss trial (cgOperator base) (cgOperator base u) l+
        referenceStep (cgOperator base) (cgOperator base u) l+
        (referenceStep (cgOperator base) (cgOperator base u) (l+1)-
          xrfcReferenceMiss trial (cgOperator base) (cgOperator base u) (l+1))) := by
  let p := oneGradientReferencePoint (xrfcMethod fullMemory trial) (cgOperator base) u
  have hmid : xrfcReferenceMidpointDrift trial (cgOperator base) u l=(1/2:ℝ) • (p (l+2)-p l) := by
    simp only [xrfcReferenceMidpointDrift,oneGradientReferenceMidpoint,ite_eq_left hl,ite_eq_left (show l<n by omega)]
    change (1/2:ℝ) • (p (l+1)+p (l+1+1))-(1/2:ℝ) • (p l+p (l+1))=_
    rw [show l+1+1=l+2 by omega]
    module
  rw [hmid]
  dsimp only [p]
  rw [xrfcReferencePoint_eq_virtual_sub_miss trial base hb u hc ht (l+2) (by omega),
    xrfcReferencePoint_eq_virtual_sub_miss trial base hb u hc ht l (by omega)]
  have hprev : xrfcPreviousMiss trial (cgOperator base) (cgOperator base u) (l+2)=
      xrfcReferenceMiss trial (cgOperator base) (cgOperator base u) (l+1) := by
    rw [xrfcPreviousMiss,ite_eq_right (by omega),show l+2-1=l+1 by omega]
  rw [hprev,show l+2=(l+1)+1 by omega,fcQuadraticReferencePoint,
    CG.displacement_succ,CG.displacement_succ]
  dsimp only [fcQuadraticReferencePoint,referenceStep]
  module

/-- The terminal compatible midpoint difference has exactly the original
half last step plus previous trial miss. Article: thm:V, xi_(n-1). -/
theorem xrfcReferenceMidpointDrift_terminal
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i)) :
    xrfcReferenceMidpointDrift trial (cgOperator base) u (n-1)=
      (1/2:ℝ) • (xrfcPreviousMiss trial (cgOperator base) (cgOperator base u) (n-1)+
        referenceStep (cgOperator base) (cgOperator base u) (n-1)) := by
  let m := xrfcMethod fullMemory trial
  let Q := cgOperator base
  have hzero := xrfcReferenceOutput_zero trial base hb u hc ht
  have hvirt := (xrfc_full_reference trial Q (cgOperator_positive base hb).1
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
  simp only [xrfcReferenceMidpointDrift,show n-1+1=n by omega,oneGradientReferenceMidpoint,
    ite_eq_right (show ¬n<n by omega),ite_eq_left (show n-1<n by omega),hzero]
  rw [xrfcReferencePoint_eq_virtual_sub_miss trial base hb u hc (fun i hi=>(ht i hi).ne') (n-1) (by omega),hp]
  module

end
end krylov.Convergence
