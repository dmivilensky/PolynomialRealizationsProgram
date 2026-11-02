import krylov.Cancellation.DeferredDataResidualResponse
import krylov.Envelope.TiltLastIncrement
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, actual full-cycle arbitrary-estimate first variation.
Use: identify the original native returned canonical gradient derivative with
the literal printed deferred spatial response on a genuine full-atom reference.
Source: proved actual arbitrary-observed-estimate residual response, primitive
native C-two regularity, true common-tilt splitting and full CG basis exhaustion.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Envelope
variable {n : ℕ}

/-- The actual full-cycle returned canonical gradient of original DC with any
positive C-two observed final estimate has precisely its printed first jet.
Use: the source spatial response is identified for the genuine original
executor, with its real reference estimate and no assumed response derivative.
Article: main_krylov, thm:DC, actual full-cycle gradient first variation.
Proof: primitive observed coefficients derive actual native C-two gradient
regularity. Its real residual vector is the proved literal deferred response.
The genuine full CG frame exhausts the ambient space and its common tilt is
zero, so actual residual splitting identifies the complete canonical derivative. -/
theorem deferred_data_full_hasDerivAt
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hB : ∀ j<k+1,ContDiffAt ℝ 2 (fun t => B t j) 0) (hB0 : B 0=fun _ => cgOperator base)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha :
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)) :
    let Q := cgOperator base
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let m := deferredDataMethod fullMemory (k+1) estimate
    let A := canonicalFCPath base E
    HasDerivAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (probedGradient m (A t) (B t) g (k+1)))
      (deferredResponse base g k (1-CG.length Q g k/a0) E) 0 := by
  let Q := cgOperator base
  let m := deferredDataMethod fullMemory (k+1) estimate
  let A := canonicalFCPath base E
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) g k)
  let epsilon := 1-CG.length Q g k/a0
  let G := fun t => probedGradient m (A t) (B t) g (k+1)
  let C := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  have hN : k+1≤referenceAtomCount base hb g := by omega
  have hpre (j : ℕ) (hj : j<k+1) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (hj.trans_le hN)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun t => A t j) 0 := (canonicalFCPath_calculus base E j).1.contDiffAt
  have hA0 : A 0=fun _ => Q := canonicalFCPath_zero base E
  have hsmooth := deferred_data_smoothCycleAt fullMemory (fun _ hj => hj) (k+1) estimate Q hQ hpos g (k+1)
    hpre 2 (fun j _ hj => by
      have he : j=k := by omega
      subst j
      exact ha)
    (fun j _ hj => by
      have he : j=k := by omega
      subst j
      exact ha0)
  have hconsistent := deferred_data_consistent fullMemory (fun _ hj => hj) (k+1) estimate (E := EuclideanSpace ℝ (Fin n))
  have hG : ContDiffAt ℝ 2 G 0 := smoothProbed_gradient_regular m hconsistent A B (fun _ => g) 0 (k+1)
    (fun j _ => hA j) hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hsmooth
  have hres := deferred_data_residualVariation estimate base hb g E hE B k hB hB0 hN ha ha0
  have hsplit := actual_tilt_splitting fullMemory m hconsistent (deferred_data_span_restricted fullMemory (k+1) estimate)
    A B g base hb hA0 hB0 (k+1) (fun j _ => hA j) hB hN hsmooth
  have hflag : exploredFlag base g (k+1)=⊤ := by
    rw [hfull]
    exact (canonicalCG_frame_of_full_atoms base hb g hcount).linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  have hproj : (exploredFlag base g (k+1)).starProjection (C (deriv G 0))=C (deriv G 0) :=
    (exploredFlag base g (k+1)).starProjection_eq_self_iff.mpr (by rw [hflag];trivial)
  rw [hproj,hres,commonTilt_exhausted base hb g A (k+1) (by omega),sub_zero] at hsplit
  have hd := C.hasFDerivAt.comp_hasDerivAt 0 (hG.differentiableAt (by norm_num)).hasDerivAt
  rwa [hsplit] at hd

end
end krylov.Cancellation
