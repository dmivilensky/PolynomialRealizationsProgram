import krylov.Envelope.XRFCTrialDelta
import krylov.Envelope.XRFCSourceEnvelope
set_option autoImplicit false
/-!
Article: Corollary B.13 [thm:E1] of krylov.tex.
Use: prove that genuine exact reference trials remove every actual XRFC output and virtual-injection trial term and recover precisely the original measured-CG canonical frozen response.
Source: actual consecutive trial-delta decomposition, proved native output coefficient and delta cancellation, and genuine inverse-root polynomial commutation.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Polynomial krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators
variable {n : ℕ}

/-- Genuine exact reference trials make the actual XRFC virtual-launch envelope response equal precisely the original common canonical frozen injection response.
Use: Genuine exact reference trials make the actual XRFC virtual-launch envelope response equal precisely the original common canonical frozen injection response.
Article: main_krylov, thm:E1, exact-trial recovery of the original common norm envelope.
Proof: The true trial deltas and native output amplitudes vanish on every actual used prefix. Commute the genuine inverse root through each real continuation and identify its actual remaining injection with the original CG source injection. -/
theorem xrfc_exact_trials_envelope_response (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k))
    (he : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)=CG.length (cgOperator base) g i) :
    xrfcEnvelopeResponse trial (canonicalFCPath base E) (fun t => canonicalFCPath base E t N) base g N=
      canonicalFrozenResponse base g (canonicalFCPath base E) N := by
  let Q := cgOperator base
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let zeta := injectionDifference (xrfcInjectionJet trial (canonicalFCPath base E) Q g)
  -- Genuine exact reference trials remove the actual trial deltas on every true earlier finite prefix.
  have hdelta (k : ℕ) (hk : k≤N) : xrfcTrialDelta trial base g E k=0 :=
    xrfcTrialDelta_exact trial base hb g E k (hk.trans hcount) (fun i hi => ht i (hi.trans_le hk))
      (fun i hi => hT i (hi.trans_le hk)) (fun i hi => he i (hi.trans_le hk))
  have hzeta (j : ℕ) (hj : j<N) : R (zeta (j+1))=
      R (referenceInjection Q g (canonicalFCPath base E) (j+1)) := by
    have h := xrfc_virtual_injection_decomposition trial base g E j
    rw [hdelta (j+1) (by omega),hdelta j hj.le,add_zero,sub_zero] at h
    exact h
  -- Every actual native output trial amplitude vanishes at its genuine measured exact reference line.
  have hzero : (∑ l∈Finset.range N,xrfcTrialCoefficient trial base g N l • cgOperator (E l) (canonicalCGUnitStep base g l))=0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [xrfcTrialCoefficient_exact trial base g N l (he l (Finset.mem_range.mp hl)),zero_smul]
  -- Compare the actual real continuation impulse sums after their genuine canonical injections have been identified.
  rw [xrfc_source_envelope_response trial base hb g E N hcount ht,hzero,add_zero]
  unfold canonicalFrozenResponse
  rw [frozen_response_formula,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [canonical_polynomial_action base hb,canonical_polynomial_action base hb]
  have hz := hzeta j (Finset.mem_range.mp hj)
  exact congrArg (fun v => (aeval Q.toLinearMap
    (phi (CG.length Q g) (CG.beta Q g) (j+1) (N-(j+1)))) v) hz
end
end krylov.Envelope
