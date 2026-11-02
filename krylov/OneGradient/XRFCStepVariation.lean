import krylov.OneGradient.XRFCLaunchDictionary
import krylov.OneGradient.XRFCLaunchPath
import krylov.OneGradient.XRFCLaunch
import krylov.OneGradient.XRFCSharp
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, genuine full-cycle step-basis XRFC first variation.
Use: identify the original printed step response with the derivative of the
actual implemented output on arbitrary varying physical operator prefixes.
Source: primitive actual query regularity, real chronological full-model
launch dictionary, genuine model-error differentiation and actual amplitude telescoping.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true full-cycle step-basis XRFC semantic output has exactly the
source's printed first derivative, derived from primitive physical data and trial charts.
Use: the operators vary throughout the actual evaluated prefix and unevaluated
output segment; no desired response or trajectory derivative is assumed.
Article: main_krylov, thm:I, step-basis response.
Proof: actual query induction gives the true moving columns and incoming
gradient. Their genuine full-column domain and chronological model dictionary
allow the proved actual launch first variation. The real reference evaluated
launch error is -a_last shat_last; genuine oblique amplitude telescoping gives
the printed a_l Pi_l transpose E_l shat_l sum, including vanishing amplitudes. -/
theorem xrfc_step_output_first_jet
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcMethod fullMemory trial
    let op := fun t k => cgOperator (A t k)
    let R := cgOperator (metricRoot base)⁻¹
    let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
    HasDerivAt (fun t => R (m.outputGradient (op t n) (oneGradientRun m (op t) g n)))
      (xrfcStepResponse trial base g E) 0 := by
  let m := xrfcMethod fullMemory trial
  let op := fun t k => cgOperator (A t k)
  let S := xrfcPathColumns trial A g
  let G := fun t => oneGradientGradient m (op t) g n
  let R := cgOperator (metricRoot base)⁻¹
  let E := fun l => R*(deriv (fun t => op t (l+1)) 0-deriv (fun t => op t l) 0)*R
  let P := fun l => transportedFlag (xrfcCanonicalColumns trial base g) l
  let C := ∑ l∈Finset.range n,cgOperator (P l)ᵀ*E l*cgOperator (P l)
  have hdata := xrfc_launch_data_contDiff trial base hb g hc A hA hA0 ht hT
  have hS0 : S 0=xrfcPhysicalColumns trial base g := xrfc_path_columns_reference trial base A hA0 g
  have hu : IsUnit (S 0).det := by
    rw [hS0]
    exact (xrfc_columns_nonsingular trial base hb g hc ht).1
  have hfirst := launch_semantic_first_jet base hb S hdata.1 hu A hA hsym hA0 G hdata.2
  let C0 := ∑ l∈Finset.range n,cgOperator (transportedFlag (metricRoot base*S 0) l)ᵀ*
    E l*cgOperator (transportedFlag (metricRoot base*S 0) l)
  change HasDerivAt (fun t => R (launchSemanticGradient (S t) (A t) (G t))) (-(C0 (R (G 0)))) 0 at hfirst
  have hC : C0=C := by
    dsimp only [C0,C,P]
    rw [hS0]
    rfl
  rw [hC] at hfirst
  have hAx : op 0=(fun _ => cgOperator base) := funext (fun k => by simp only [op,hA0])
  have hG0 : G 0=(oneGradientRun m (fun _ => cgOperator base) g n).gradient := by
    change (oneGradientRun m (op 0) g n).gradient=_
    rw [hAx]
  have hlaunch : R (G 0)=-(xrfcTrialCoefficient trial base g n (n-1) • canonicalCGUnitStep base g (n-1)) := by
    rw [hG0]
    exact xrfc_reference_launch_error trial base hb g hc hn ht
  have hresponse : -(C (R (G 0)))=xrfcStepResponse trial base g E := by
    rw [hlaunch,map_neg,neg_neg]
    simp only [C,_root_.sum_apply,mul_apply_eq_comp,xrfcStepResponse]
    apply Finset.sum_congr rfl
    intro l hl
    have h := xrfc_projector_last_amplitude trial base hb g hc ht l (Finset.mem_range.mp hl)
    change cgOperator (P l)ᵀ (E l (cgOperator (P l)
        (xrfcTrialCoefficient trial base g n (n-1) • canonicalCGUnitStep base g (n-1))))=_
    rw [h,map_smul,map_smul]
  rw [hresponse] at hfirst
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ),IsUnit (S t).det := by
    have hu0 : IsUnit (S 0) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
    exact (hdata.1.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds hu0)).mono
      (fun t ht' => (Matrix.isUnit_iff_isUnit_det _).mp ht')
  have he : (fun t => R (m.outputGradient (op t n) (oneGradientRun m (op t) g n)))=ᶠ[𝓝 0]
      (fun t => R (launchSemanticGradient (S t) (A t) (G t))) := by
    filter_upwards [hunit] with t ht'
    exact congrArg R (xrfc_semantic_launch_dictionary trial (A t) g ht')
  dsimp only
  exact hfirst.congr_of_eventuallyEq he

end
end krylov.OneGradient
