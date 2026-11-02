import krylov.Envelope.XRFCOutputJet
import krylov.Envelope.CanonicalFiltration
import krylov.Envelope.CompactNormVariation
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual canonical virtual-launch norm first variation.
Use: remove the genuine virtual Krylov displacement remainder by true reference-error orthogonality and retain the actual propagated effective injections plus original output defect.
Source: proved actual XRFC frozen filtration, genuine semantic output first jet and original positive-root CG flag geometry.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators
variable {n : ℕ}

/-- The genuine canonical propagated actual virtual-injection response plus the real primitive unevaluated output-defect first variation.
Use: The genuine canonical propagated actual virtual-injection response plus the real primitive unevaluated output-defect first variation.
Article: main_krylov, thm:E1, actual canonical virtual-launch norm first variation.
Proof: Apply the actual inverse metric root to the true measured-CG frozen executor and explicit native reference output defect. -/
def xrfcEnvelopeResponse (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (frozenResponse (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
      (injectionDifference (xrfcInjectionJet trial A (cgOperator base) g)) N 0+
      xrfcOutputJet trial A B (cgOperator base) g N)

/-- The actual semantic XRFC output first derivative has exactly the printed virtual-envelope pairing with the genuine nonexhausted reference error.
Use: The actual semantic XRFC output first derivative has exactly the printed virtual-envelope pairing with the genuine nonexhausted reference error.
Article: main_krylov, thm:E1, actual canonical virtual-launch norm first variation.
Proof: The real effective-gradient frozen remainder is the original reference-operator image of a true Krylov vector. Actual root cancellation puts its canonical image in the genuine explored flag, which the original CG error annihilates. -/
theorem xrfc_norm_first_jet_pairing (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hcount : N<referenceAtomCount base hb g)
    (hA0 : A 0=fun _ => cgOperator base) (hB0 : B 0=cgOperator base)
    (hA : ∀ i,ContDiffAt ℝ 2 (fun t => A t i) 0) (hB : ContDiffAt ℝ 2 B 0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A 0) g k)) :
    let m := xrfcMethod fullMemory trial
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    inner ℝ (cgCanonicalError base g N)
      (R (deriv (fun t => m.outputGradient (B t) (oneGradientRun m (A t) g N)) 0))=
      inner ℝ (cgCanonicalError base g N) (xrfcEnvelopeResponse trial A B base g N) := by
  dsimp only
  let Q := cgOperator base
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let dg := deriv (fun t => xrfcVirtualGradient trial (A t) g N) 0
  let F := frozenResponse Q (CG.length Q g) (CG.beta Q g)
    (injectionDifference (xrfcInjectionJet trial A Q g)) N 0
  let D := xrfcOutputJet trial A B Q g N
  let e := cgCanonicalError base g N
  let P := exploredFlag base g N
  have hpre (i : ℕ) (hi : i≤N) : CG.gradient Q g i≠0 := cg_nonstagnation base hb g i (hi.trans_lt hcount)
  have hp := cgOperator_positive base hb
  -- Use the true actual virtual frozen theorem before discarding its genuine explored Krylov remainder.
  have hfil := (xrfc_frozen_filtration trial A g Q hp.1 hp.2 hA0 N hA hpre ht hT N le_rfl).2
  obtain ⟨v,hv,he⟩ := hfil
  have hflag : R dg-R F∈P := by
    rw [← map_sub,← he]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (cgOperator base v)∈P
    rw [canonical_reference_action base hb]
    dsimp only [P]
    rw [exploredFlag_eq_primal_krylov base hb g N (fun i hi => hpre i hi.le)]
    exact Submodule.mem_map_of_mem hv
  have ho : inner ℝ e (R dg-R F)=0 := by
    rw [real_inner_comm]
    exact exploredFlag_error_orthogonal base hb g hcount.le _ hflag
  -- The actual unevaluated output defect survives; only the true explored effective-gradient remainder is orthogonal to the reference error.
  have hd := xrfc_output_first_jet trial A B g Q hp.1 hp.2 hA0 hB0 N hA hB
    (fun i hi => hpre i hi.le) ht hT
  rw [hd]
  change inner ℝ e (R (dg+D))=inner ℝ e (R (F+D))
  rw [map_add,map_add,inner_add_right,inner_add_right]
  have heq : inner ℝ e (R dg)=inner ℝ e (R F) := by rw [inner_sub_right] at ho;linarith
  rw [heq]
end
end krylov.Envelope
