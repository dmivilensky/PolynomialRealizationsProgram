import krylov.Cancellation.DCConsistentCycle
import krylov.Cancellation.DeferredFullProfile
import krylov.Envelope.ResidualOrders
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), actual consistent DC-slide sharp first variation.
Use: identify the genuine returned-gradient derivative under original C-one
estimates and prove its exact attained matrix-budget maximum in the printed
last-error norm.
Source: the proved true native C-one quadratic cycle remainder, the reused
superlinear-order derivative criterion and genuine symmetric matrix attainers.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Filter Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Envelope
open scoped Topology Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true full-cycle canonical gradient of consistent original C-one
DC-slide has exactly the calibrated deferred fresh-response derivative.
Use: this is a derivative of the original executor, not of an assumed response.
Article: main_krylov, apH:dcs2(b), original native first-order equality.
Proof: the genuine full-basis cycle remainder is quadratic under C-one data.
Its actual derivative is zero by the proved superlinear-order criterion;
add the exact linear calibrated deferred response back to the actual output. -/
theorem dc_slide_consistent_full_hasDerivAt
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha : ∀ j<k+1,
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => cgOperator base) (fun _ => cgOperator base) g j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ j<k+1,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j))
    (hcal : ∀ j<k+1,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j)=CG.length (cgOperator base) g j)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm) :
    let m := dcSlideMethod fullMemory estimate
    HasDerivAt (fun t : ℝ => cgOperator (metricRoot base)⁻¹
      (probedGradient m (canonicalFCPath base E t) (canonicalFCPath base E t) g (k+1)))
      (deferredResponse base g k 0 E) 0 := by
  let m := dcSlideMethod fullMemory estimate
  let Phi := fun t : ℝ => cgOperator (metricRoot base)⁻¹
    (probedGradient m (canonicalFCPath base E t) (canonicalFCPath base E t) g (k+1))
  let L := deferredResponse base g k 0 E
  have hO := dc_slide_consistent_canonical_order estimate base hb g k hcount hfull E hE
    (canonicalFCPath base E) (fun j _ => (canonicalFCPath_calculus base E j).1.contDiffAt)
    (canonicalFCPath_zero base E) ha ha0 hcal
  have hrem : HasDerivAt (fun t => Phi t-t • L) 0 0 :=
    hasDerivAt_zero_of_norm_order _ 2 (by omega) hO
  have hline : HasDerivAt (fun t : ℝ => t • L) L 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const L using 1
    simp only [one_smul]
  have hadd := hrem.add hline
  change HasDerivAt (fun t : ℝ => Phi t-t • L+t • L) (0+L) 0 at hadd
  have heq : (fun t : ℝ => Phi t-t • L+t • L)=Phi := by funext t;abel
  rw [heq,zero_add] at hadd
  exact hadd

/-- Consistent native C-one DC-slide attains exactly the original
correction-free first-order minimax value over actual symmetric source
matrix budgets, expressed in the printed last true error norm.
Use: proves sharpness for the actual sliding executor, with genuine attaining
matrices and all zero budgets, after reconstructing its full terminal vector.
Article: main_krylov, apH:dcs2(b), sharp W0 times last-error value.
Proof: every actual output derivative is the proved calibrated deferred
response. Its genuine symmetric matrix maximum was attained explicitly;
true last-step energy telescoping gives the literal source last-error norm. -/
theorem dc_slide_consistent_first_order_sharp
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha : ∀ j<k+1,
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => cgOperator base) (fun _ => cgOperator base) g j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ j<k+1,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j))
    (hcal : ∀ j<k+1,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j)=CG.length (cgOperator base) g j)
    (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    let m := dcSlideMethod fullMemory estimate
    IsGreatest {z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧
      z=‖deriv (fun t : ℝ => cgOperator (metricRoot base)⁻¹
        (probedGradient m (canonicalFCPath base E t) (canonicalFCPath base E t) g (k+1))) 0‖}
      ((∑ l∈range k,omega l)*‖cgCanonicalError base g k‖) := by
  have hN : k+1≤referenceAtomCount base hb g := by omega
  have hsharp := deferred_response_sharp base hb g k hN 0 omega homega
  have hc : (∑ l∈range k,omega l*Real.sqrt (cgEnergy base g k+
      (0 : ℝ)^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2)))=
      (∑ l∈range k,omega l)*‖cgCanonicalError base g k‖ := by
    simp only [zero_pow (by decide : (2 : ℕ)≠0),zero_mul,add_zero]
    rw [← Finset.sum_mul,last_energy_error_norm base hb g k (by omega)]
  rw [hc] at hsharp
  constructor
  · obtain ⟨E,hE,hbudget,hvalue⟩ := hsharp.1
    refine ⟨E,hE,hbudget,?_⟩
    rw [(dc_slide_consistent_full_hasDerivAt estimate base hb g k hcount hfull ha ha0 hcal E hE).deriv]
    exact hvalue
  · rintro z ⟨E,hE,hbudget,rfl⟩
    rw [(dc_slide_consistent_full_hasDerivAt estimate base hb g k hcount hfull ha ha0 hcal E hE).deriv]
    exact hsharp.2 ⟨E,hE,hbudget,rfl⟩

end
end krylov.Cancellation
