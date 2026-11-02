import krylov.Envelope.XRFCCanonicalTrialFormulas
import krylov.Envelope.XRFCNormEnvelope
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, complete printed virtual-launch source envelope.
Use: express the actual semantic XRFC canonical norm expansion with genuine measured continuation polynomials, actual consecutive virtual injections and the original printed trial-amplitude output sum.
Source: actual full virtual frozen filtration, native output increment formula, real continuation impulse unrolling and proved genuine quadratic norm remainder.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Polynomial krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators
variable {n : ℕ}

/-- The genuine XRFC virtual-envelope response on the original canonical source path is exactly the printed measured-continuation virtual-injection sum plus actual trial-amplitude output increments.
Use: The genuine XRFC virtual-envelope response on the original canonical source path is exactly the printed measured-continuation virtual-injection sum plus actual trial-amplitude output increments.
Article: main_krylov, thm:E1, complete printed virtual-launch source envelope.
Proof: Unroll the real measured-CG frozen executor and substitute the proved actual canonical native output formula. -/
theorem xrfc_source_envelope_response (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0) :
    let Q := cgOperator base
    let zeta := injectionDifference (xrfcInjectionJet trial (canonicalFCPath base E) Q g)
    xrfcEnvelopeResponse trial (canonicalFCPath base E) (fun t => canonicalFCPath base E t N) base g N=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
        (∑ j∈Finset.range N,(aeval Q.toLinearMap
          (phi (CG.length Q g) (CG.beta Q g) (j+1) (N-(j+1)))) (zeta (j+1)))+
      ∑ l∈Finset.range N,xrfcTrialCoefficient trial base g N l • cgOperator (E l) (canonicalCGUnitStep base g l) := by
  dsimp only
  rw [xrfcEnvelopeResponse,map_add,frozen_response_formula,xrfc_canonical_output_formula trial base hb g E N hcount ht]

/-- The actual canonical semantic full-memory XRFC output on the original canonical source scenario has the printed virtual-launch norm envelope with a genuine weighted quadratic remainder.
Use: The actual canonical semantic full-memory XRFC output on the original canonical source scenario has the printed virtual-launch norm envelope with a genuine weighted quadratic remainder.
Article: main_krylov, thm:E1, complete printed virtual-launch source envelope.
Proof: Insert the actual constructed primitive canonical path and native trial-coordinate domains into the proved real output norm theorem, then identify its genuine continuation and trial-amplitude response. -/
theorem xrfc_source_norm_envelope (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (hcount : N<referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcMethod fullMemory trial
    let Q := cgOperator base
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    let e := cgCanonicalError base g N
    let e0 := ‖R g‖
    let zeta := injectionDifference (xrfcInjectionJet trial (canonicalFCPath base E) Q g)
    let response := R (∑ j∈Finset.range N,(aeval Q.toLinearMap
      (phi (CG.length Q g) (CG.beta Q g) (j+1) (N-(j+1)))) (zeta (j+1)))+
      ∑ l∈Finset.range N,xrfcTrialCoefficient trial base g N l • cgOperator (E l) (canonicalCGUnitStep base g l)
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      |‖R (m.outputGradient (canonicalFCPath base E t N) (oneGradientRun m (canonicalFCPath base E t) g N))‖-
        ‖e‖-t*inner ℝ e response/‖e‖|≤C*t^2*e0*(1+e0/‖e‖) := by
  have h := xrfc_norm_envelope trial (canonicalFCPath base E) (fun t => canonicalFCPath base E t N)
    base hb g N hcount (canonicalFCPath_zero base E) (congrFun (canonicalFCPath_zero base E) N)
    (fun i => (canonicalFCPath_calculus base E i).1.contDiffAt) (canonicalFCPath_calculus base E N).1.contDiffAt ht
    (by rw [canonicalFCPath_zero];exact hT)
  dsimp only at h ⊢
  rw [xrfc_source_envelope_response trial base hb g E N hcount.le ht] at h
  exact h
end
end krylov.Envelope
