import krylov.OneGradient.KnownBaseCentredMethod
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), actual centred-method observed column.
Use: the real centred M1 implementation observes precisely the unknown
second operator's column on the known final CG step, without an asymptotic
substitution of its query vectors or returned gradient.
Source: true output-free query recursion, exact informed calibrated queries
and the actual final CG residual identity.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace

/-- Every real evaluated centring query is exactly the genuine informed
query on arbitrary varying operators, independently of the final output.
Use: native query calibration concerns the actual attaining candidate.
Article: main_krylov, thm:local(c), actual centring query dictionary.
Proof: the true full histories coincide and the real step fields are equal. -/
theorem knownBaseCentredMethod_steps (base : Matrix (Fin 2) (Fin 2) ℝ) (eta : ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (g : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    oneGradientStep (knownBaseCentredMethod base eta) A g k=
      oneGradientStep (xrfcMethod fullMemory (informedTrial (cgOperator base))) A g k := by
  unfold oneGradientStep
  rw [knownBaseCentredMethod_histories]
  rfl

/-- The actual centring candidate's last returned gradient is exactly the
unknown second-segment difference acting on the known final CG step.
Use: the centring output reads an exact observed unknown column, not a
first-order approximation with uncontrolled boundary errors.
Article: main_krylov, thm:local(c), true observed final gradient.
Proof: the actual first two queries are the known CG steps. The genuine
first returned gradient is the first CG residual; the true zero final CG
residual cancels its known second operator action, leaving the exact drift. -/
theorem knownBaseCentredMethod_last_gradient (base : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : base.PosDef) (eta : ℝ) (C : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2) :
    (oneGradientRun (knownBaseCentredMethod base eta) (twoQueryOperators (cgOperator base) C) g 2).gradient=
      (C-cgOperator base) (referenceStep (cgOperator base) g 1) := by
  let Q := cgOperator base
  let m := knownBaseCentredMethod base eta
  let A := twoQueryOperators Q C
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<2,CG.gradient Q g i≠0 := fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hq := informed_two_queries Q C hp.1 hp.2 g hpre
  have hfirst : oneGradientStep m A g 0=referenceStep Q g 0 :=
    (knownBaseCentredMethod_steps base eta A g 0).trans hq.1
  have hlast : oneGradientStep m A g 1=referenceStep Q g 1 :=
    (knownBaseCentredMethod_steps base eta A g 1).trans hq.2
  have hG1 : (oneGradientRun m A g 1).gradient=CG.gradient Q g 1 := by
    change g+Q (oneGradientStep m A g 0)=_
    rw [hfirst,referenceStep,map_smul]
    rfl
  change (oneGradientRun m A g 1).gradient+C (oneGradientStep m A g 1)=_
  rw [hG1,hlast,_root_.sub_apply]
  have hzero : CG.gradient Q g 1+Q (referenceStep Q g 1)=0 := by
    rw [referenceStep,map_smul,← CG.gradient_succ]
    have h := cg_terminates base hb g
    rw [hc] at h
    exact h
  have he := eq_neg_of_add_eq_zero_left hzero
  rw [he]
  abel

end
end krylov.OneGradient
