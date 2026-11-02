import krylov.Convergence.OneGradientLocalization
import krylov.Stability.ContDiffXRFCD
import krylov.Convergence.VirtualDirectionHomogeneous

/-!
Article: main_krylov, thm:V and hypotheses V1--V2.
Use: discharge the generic scalar-query localization hypotheses from the
original primitive observed trial charts of the actual XRFC policy. Neither
native query bounds nor regularity of a supplied trajectory is assumed.
Source: genuine quadratic XRFC inverse domains, actual C-two query induction,
and the proved degree-zero observed-trial homogeneity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Primitive C-two trial charts imply C-one actual finite XRFC query
fields at every genuine positive full reference. Article: V1, thm:V. -/
theorem xrfcDFiniteField_contDiffAt
    (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (g : E) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>Q) g i)≠0)
    (hT : ∀ i<N,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>Q) g i)) :
    ContDiffAt ℝ 1 (oneGradientFiniteField (xrfcDMethod fullMemory trial) Q N) (g,0) := by
  let A := fun z : E × (Fin N → E →L[ℝ] E)=>fcFiniteOperatorPath Q N z.2
  have hA i : ContDiffAt ℝ 1 (fun z=>A z i) (g,0) :=
    (fcFiniteOperatorPath_analytic Q N i (g,0)).contDiffAt
  have hAz : A (g,0)=fun _=>Q := fcFiniteOperatorPath_zero Q N
  have hT' : ∀ i<N,ContDiffAt ℝ 1 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (A (g,0)) g i) := by
    intro i hi
    rw [hAz]
    exact (hT i hi).of_le (by norm_num)
  have hp := quadraticXRFCD_prefix_contDiffAt trial A Prod.fst (g,0) hA contDiffAt_fst
    Q hAz hQ hpos N hpre ht hT'
  have ho := quadraticXRFCD_output_contDiffAt trial A (fun _=>Q) Prod.fst (g,0) hA contDiffAt_const
    contDiffAt_fst Q hAz hQ hpos N hpre ht hT'
  have hd : ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>
        (oneGradientRun (xrfcDMethod fullMemory trial) (A z) z.1 N).displacement) (g,0) := by
    simp only [oneGradientRun_displacement_sum]
    exact ContDiffAt.sum fun i hi=>hp.2.1 i (mem_range.mp hi)
  have hout : ContDiffAt ℝ 1
      (fun z : E × (Fin N → E →L[ℝ] E)=>
        (xrfcDMethod fullMemory trial).output (oneGradientRun (xrfcDMethod fullMemory trial) (A z) z.1 N)) (g,0) := by
    convert ho.1.sub hd using 1
    funext z
    unfold OneGradientMethod.outputDisplacement
    abel
  exact (contDiffAt_pi.mpr fun i : Fin N=>hp.2.1 i.val i.isLt).prodMk hout

omit [CompleteSpace E] in
/-- The actual XRFC query and unevaluated correction are homogeneous
under precisely the primitive degree-zero trial rule. Article: V2, thm:V. -/
theorem xrfcD_policy_homogeneous (trial : History E → ℝ) (hhom : ObservedTrialHomogeneous trial)
    (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    (∀ i<N,oneGradientStep (xrfcDMethod fullMemory trial) A (c • g) i=
      c • oneGradientStep (xrfcDMethod fullMemory trial) A g i) ∧
    (xrfcDMethod fullMemory trial).output (oneGradientRun (xrfcDMethod fullMemory trial) A (c • g) N)=
      c • (xrfcDMethod fullMemory trial).output (oneGradientRun (xrfcDMethod fullMemory trial) A g N) := by
  have hp := xrfcD_scalar_prefix trial hhom A g c hc N
  have hv := xrfcD_virtualBlock_scalar trial A g N c hc.ne' hp.2.2.1 hp.2.2.2 (hp.1 N le_rfl)
  exact ⟨hp.2.1,hv.1⟩

/-- The original compact direction family's full atom condition and
primitive trial charts discharge every genuine C-one finite-field premise.
Article: V1--V3, thm:V. -/
theorem xrfcDFiniteField_contDiffAt_directions {n : ℕ}
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)) :
    ∀ g∈(cgOperator base) '' U,ContDiffAt ℝ 1
      (oneGradientFiniteField (xrfcDMethod fullMemory trial) (cgOperator base) n) (g,0) := by
  rintro g ⟨u,hu,rfl⟩
  exact xrfcDFiniteField_contDiffAt trial _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 n (cgOperator base u)
    (fun i hi=>cg_nonstagnation base hb (cgOperator base u) i (by rw [hcount u hu]; exact hi))
    (fun i hi=>(ht u hu i hi).ne') (hT u hu)

end
end krylov.Convergence
