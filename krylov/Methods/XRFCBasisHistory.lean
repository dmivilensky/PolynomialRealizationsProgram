import krylov.Methods.DirectionReference
import krylov.Methods.XRFCShortPrefix
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, identical original quadratic histories in both XRFC bases.
Use: both source response formulas use the same actual measured trials and
amplitudes, even for arbitrary data-dependent original trial rules.
Source: genuine virtual quadratic consistency in each basis, proved on their
real observed executions; no equality of trial sequences is assumed.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original full-memory step and direction implementations have identical
complete real quadratic histories and hence identical data-dependent trials.
Use: identify the actual direction-basis trial amplitudes with the original
measured coefficients used in the source response and sharp constants.
Article: main_krylov, thm:I.
Proof: strong induction identifies every earlier observed history and thereby
derives all direction-basis nonzero trials. The two actual virtual reference
identities give the same correction point and CG direction at the next query;
the genuine one-gradient update then records exactly the same step and gradient. -/
theorem xrfc_quadratic_basis_histories (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k=
      oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => rfl
    | succ j =>
      let mD := xrfcDMethod fullMemory trial
      let mS := xrfcMethod fullMemory trial
      let HD := oneGradientRun mD (fun _ => Q) g j
      let HS := oneGradientRun mS (fun _ => Q) g j
      have hh : HD=HS := ih j (by omega) (by omega)
      have htD (i : ℕ) (hi : i<j+1) : trial (oneGradientRun mD (fun _ => Q) g i)≠0 := by
        change trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0
        rw [ih i hi (by omega)]
        exact ht i (by omega)
      have hvD := xrfcD_reference fullMemory trial Q hQ hpos g (j+1)
        (fun i hi => hpre i (by omega)) (fun _ _ hi => hi) htD j (by omega)
      have hvS := xrfc_full_reference trial Q hQ hpos g N hpre ht j (by omega)
      have hcor : mD.output HD=mS.output HS := by
        have hD : HD.displacement+mD.output HD=CG.displacement Q g j := hvD.1
        have hS : HS.displacement+mS.output HS=CG.displacement Q g j := hvS.1
        rw [hh] at hD
        rw [hh]
        exact add_left_cancel (hD.trans hS.symm)
      have hsD : mD.step HD=mD.output HD+trial HD • CG.direction Q g j := by
        change virtualCorrection (selectedDirectionWindow fullMemory trial HD) HD.gradient+
          trial HD • windowDirection (selectedDirectionWindow fullMemory trial HD)
            (virtualGradient (selectedDirectionWindow fullMemory trial HD) HD.gradient)=_
        rw [hvD.2.2]
        rfl
      have hsS : mS.step HS=mS.output HS+trial HS • CG.direction Q g j := by
        change virtualCorrection (selectedWindow fullMemory HS) HS.gradient+
          trial HS • windowDirection (selectedWindow fullMemory HS)
            (virtualGradient (selectedWindow fullMemory HS) HS.gradient)=_
        rw [selectedWindow_full,hvS.2.2]
        change virtualCorrection HS.pairs HS.gradient+trial HS • CG.direction Q g j=
          virtualCorrection (selectedWindow fullMemory HS) HS.gradient+trial HS • CG.direction Q g j
        rw [selectedWindow_full]
      have hstep : mD.step HD=mS.step HS := by rw [hsD,hsS,hcor,hh]
      change oneGradientAdvance mD Q HD=oneGradientAdvance mS Q HS
      rw [hh] at hstep
      simp only [oneGradientAdvance,hh,hstep]

/-- The same complete quadratic history equality with nonzero actual
reference trials supplied in the original direction implementation.
Use: identify the true direction-basis amplitudes without a separate step-run
nonzero-trial hypothesis.
Article: main_krylov, thm:I.
Proof: strong induction transfers each original nonzero direction trial to
the step run using the already proved shorter-prefix history equality.
The full proved history theorem then applies with those derived real trials. -/
theorem xrfc_quadratic_basis_histories_of_direction (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k=
      oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g k := by
  have hS : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      have hshort : ∀ j < i,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g j)≠0 :=
        fun j hj => ih j hj (hj.trans hi)
      rw [← xrfc_quadratic_basis_histories trial Q hQ hpos g i
        (fun j hj => hpre j (hj.trans hi)) hshort i le_rfl]
      exact ht i hi
  exact xrfc_quadratic_basis_histories trial Q hQ hpos g N hpre hS k hk

end
end krylov.Methods
