import krylov.OneGradient.XRFCStepVariation
import krylov.Stability.FirstOrderTaylor
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, actual step-basis output expansion and quadratic remainder.
Use: close the printed varying-prefix step-basis XRFC expansion with a
true radius and error constant from original primitive C2 trial data.
Source: the proved actual full-cycle step response, genuine primitive output
regularity and the reused real C2 first-order Taylor remainder.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original full-memory step-basis XRFC output has the complete printed
first-order response with a true quadratic error on every smooth physical prefix path.
Use: all evaluated segment operators and the unevaluated output operator may
vary; only original observed trial-chart C2 smoothness and genuine reference
nondegeneracy are assumed. Exact reference trials therefore leave a real quadratic error.
Article: main_krylov, thm:I, step-basis expansion.
Proof: true primitive query and output regularity gives the actual semantic
output C2. Its genuine reference gradient is zero and its proved actual
first derivative is the original measured-amplitude oblique response. Apply
the reused actual first-order Taylor theorem to that same real output. -/
theorem xrfc_step_output_quadratic_remainder
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 2 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcMethod fullMemory trial
    let op := fun t k => cgOperator (A t k)
    let R := cgOperator (metricRoot base)⁻¹
    let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖R (m.outputGradient (op t n) (oneGradientRun m (op t) g n))-
        t • xrfcStepResponse trial base g E‖≤C*t^2 := by
  let m := xrfcMethod fullMemory trial
  let op := fun t k => cgOperator (A t k)
  let R := cgOperator (metricRoot base)⁻¹
  let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
  let Phi := fun t => R (m.outputGradient (op t n) (oneGradientRun m (op t) g n))
  have hAx : op 0=(fun _ => cgOperator base) := funext (fun k => by simp only [op,hA0])
  have hAop (k : ℕ) : ContDiffAt ℝ 2 (fun t => op t k) 0 := matrixOperator_contDiffAt _ 0 (hA k)
  have hp := cgOperator_positive base hb
  have hout := (quadraticXRFC_output_contDiffAt trial op (fun t => op t n) (fun _ => g) 0
    hAop (hAop n) contDiffAt_const (cgOperator base) hAx hp.1 hp.2 n
    (fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)) ht (by rw [hAx];exact hT)).2
  have hPhi : ContDiffAt ℝ 2 Phi 0 := R.contDiff.contDiffAt.comp 0 hout
  have hzero : Phi 0=0 := by
    change R (m.outputGradient (op 0 n) (oneGradientRun m (op 0) g n))=0
    rw [hAx]
    have hterm := (xrfc_full_terminates base hb g trial (fun i hi => ht i (by rw [← hc];exact hi))).2.1
    rw [hc] at hterm
    change m.outputGradient (cgOperator base) (oneGradientRun m (fun _ => cgOperator base) g n)=0 at hterm
    rw [hterm,map_zero]
  have hjet := xrfc_step_output_first_jet trial base hb g hc hn A
    (fun k => (hA k).of_le (by norm_num)) hsym hA0 ht (fun k hk => (hT k hk).of_le (by norm_num))
  change HasDerivAt Phi (xrfcStepResponse trial base g E) 0 at hjet
  obtain ⟨delta,C,hd,hC,hbound⟩ := c2_first_order_remainder Phi (xrfcStepResponse trial base g E) hPhi hjet
  refine ⟨delta,C,hd,hC,?_⟩
  intro t ht'
  simpa only [hzero,sub_zero] using hbound t ht'

end
end krylov.OneGradient
