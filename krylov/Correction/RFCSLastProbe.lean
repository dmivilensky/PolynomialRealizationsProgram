import krylov.Correction.RFCSFullPrediction
import krylov.Correction.RFCSLineStep

/-!
Article: main_krylov, thm:RFCS, genuine only-last-probe first-order expansion.
Use: the actual independently probed RFC-S executor has only its final
probe mismatch in the true first variation, with a derived quadratic remainder.
Source: actual analytic measured histories, the genuine predicted-model
projected residual, full reference rank and exact physical mismatch balance.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {k : ℕ}

/-- The genuine physical RFC-S final output has only the original last probe-to-line mismatch applied to the true last CG step, up to a quadratic remainder.
Use: no first variation of earlier probes or of the adaptive prefix remains in the actual returned output.
Article: main_krylov, thm:RFCS, actual only-last-probe physical expansion.
Proof: the real full corrected prediction is already quadratic. Actual
analytic line-step replacement costs first order, and the primitive true
probe-to-line mismatch is first order as well. Their actual operator action
is therefore quadratic; the exact genuine output balance leaves exactly
the printed last mismatch on the original CG reference step. -/
theorem full_rfcs_last_probe_order
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (Ap A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hAp : ∀ i, AnalyticAt ℝ (fun x => Ap x i) 0)
    (hA : ∀ i, AnalyticAt ℝ (fun x => A x i) 0) (hB : ∀ i, AnalyticAt ℝ (fun x => B x i) 0)
    (hAp0 : Ap 0=(fun _ => cgOperator base)) (hA0 : A 0=(fun _ => cgOperator base))
    (hB0 : B 0=(fun _ => cgOperator base)) :
    (fun x => rfcSGradient fullMemory (Ap x) (A x) (B x) g (k+1)-
      (A x k-Ap x k) (referenceStep (cgOperator base) g k)) =O[𝓝 (0 : X)] (fun x => ‖x‖^2) := by
  -- Freeze only the final true line step; its first-order displacement multiplies the genuine first-order mismatch.
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (hi.trans_lt (Nat.lt_succ_self k) |>.trans_le hN)
  have hline := rfcSLineStep_regular fullMemory Ap A B (fun _ => g) hAp hA hB analyticAt_const
    (cgOperator base) hAp0 hA0 hB0 hp.1 hp.2 (fun _ _ hi => hi) k hpre
  have hLo : (fun x => rfcSLineStep fullMemory (Ap x) (A x) (B x) g k-referenceStep (cgOperator base) g k)
      =O[𝓝 (0 : X)] (fun x => ‖x‖) := by
    simpa only [hline.2] using analytic_reference_order _ hline.1
  have hDo : (fun x => A x k-Ap x k) =O[𝓝 (0 : X)] (fun x => ‖x‖) := by
    have ha := analytic_reference_order (fun x => A x k-Ap x k) ((hA k).sub (hAp k))
    simpa only [hA0,hAp0,sub_self,sub_zero] using ha
  have hprod := operator_action_order (fun x => A x k-Ap x k)
    (fun x => rfcSLineStep fullMemory (Ap x) (A x) (B x) g k-referenceStep (cgOperator base) g k)
    (fun x => ‖x‖) (fun x => ‖x‖) hDo hLo
  have hprod' : (fun x => (A x k-Ap x k)
      (rfcSLineStep fullMemory (Ap x) (A x) (B x) g k-referenceStep (cgOperator base) g k))
      =O[𝓝 (0 : X)] (fun x => ‖x‖^2) := by simpa only [pow_two] using hprod
  have hsum := (full_rfcs_prediction_quadratic base hb g hN hk Ap A B hAp hA hB hAp0 hA0 hB0).add hprod'
  apply hsum.congr_left
  intro x
  rw [rfcSGradient_succ,map_sub]
  abel

end
end krylov.Correction

