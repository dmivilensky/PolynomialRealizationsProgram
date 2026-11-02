import krylov.Envelope.VirtualDefectJets
import krylov.Envelope.XRFCFrozenFiltration
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual semantic unevaluated XRFC output first jet.
Use: split the true output derivative into the actual effective-gradient derivative and original reference-weighted physical output defect.
Source: exact genuine semantic output balance, primitive actual XRFC regularity and the proved native zero-defect product first jet.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The true reference-weighted physical primitive output-defect first variation of the actual XRFC unevaluated segment.
Use: The true reference-weighted physical primitive output-defect first variation of the actual XRFC unevaluated segment.
Article: main_krylov, thm:E1, actual semantic unevaluated XRFC output first jet.
Proof: Apply each genuine output-minus-segment operator derivative to its actual stored reference step with the native chronological virtual weight. -/
def xrfcOutputJet (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (B : ℝ → E →L[ℝ] E) (Q : E →L[ℝ] E) (g : E) (N : ℕ) : E :=
  ∑ i : Fin N,oneGradientVirtualCoefficients (xrfcMethod fullMemory trial) (fun _ => Q) g N i •
    (deriv B 0-deriv (fun t => A t i.val) 0) (oneGradientStep (xrfcMethod fullMemory trial) (fun _ => Q) g i.val)

/-- The genuine semantic unevaluated XRFC output derivative equals its actual effective-gradient derivative plus the true explicit physical output-defect first jet.
Use: The genuine semantic unevaluated XRFC output derivative equals its actual effective-gradient derivative plus the true explicit physical output-defect first jet.
Article: main_krylov, thm:E1, actual semantic unevaluated XRFC output first jet.
Proof: Derive actual effective-gradient and native coefficient regularity from primitive trial charts, then differentiate the exact real output balance. -/
theorem xrfc_output_first_jet (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (B : ℝ → E →L[ℝ] E) (g : E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (hA0 : A 0=fun _ => Q) (hB0 : B 0=Q)
    (N : ℕ) (hA : ∀ i,ContDiffAt ℝ 2 (fun t => A t i) 0) (hB : ContDiffAt ℝ 2 B 0)
    (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A 0) g k)) :
    let m := xrfcMethod fullMemory trial (E := E)
    deriv (fun t => m.outputGradient (B t) (oneGradientRun m (A t) g N)) 0=
      deriv (fun t => xrfcVirtualGradient trial (A t) g N) 0+xrfcOutputJet trial A B Q g N := by
  dsimp only
  let m := xrfcMethod fullMemory trial (E := E)
  -- Genuine primitive charts and original positive reference models justify the actual differentiation of the semantic output balance.
  have hreg := quadraticXRFC_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const Q hA0 hQ hpos N hpre ht hT
  have hdom := xrfc_full_array_domains trial Q hQ hpos g N hpre ht N le_rfl
  have hM : (pairModel
      (fun i : Fin N => oneGradientStep m (A 0) g (N-1-i.val))
      (fun i : Fin N => A 0 (N-1-i.val) (oneGradientStep m (A 0) g (N-1-i.val)))).det≠0 := by
    rw [hA0]
    exact hdom.2
  have hG : ContDiffAt ℝ 2 (fun t => xrfcVirtualGradient trial (A t) g N) 0 :=
    (oneGradient_virtualBlock_contDiffAt m A (fun _ => g) 0 N (fun i _ => hA i) hreg.2 (hreg.1 N le_rfl)
      hM (by rw [hA0];exact hdom.1)).2.1
  have hD := virtualOutputDefect_hasDeriv m A B Q g N hA0 hB0
    (fun i _ => (hA i).of_le (by norm_num)) (hB.of_le (by norm_num))
    (fun i hi => (hreg.2 i hi).of_le (by norm_num)) ((hreg.1 N le_rfl).of_le (by norm_num)) hM
  have hd := ((hG.differentiableAt (by norm_num)).hasDerivAt.add hD)
  have he : (fun t => m.outputGradient (B t) (oneGradientRun m (A t) g N))=
      fun t => xrfcVirtualGradient trial (A t) g N+virtualOutputDefect m (A t) (B t) g N := by
    funext t
    exact xrfc_virtual_output_balance trial (A t) (B t) g N
  rw [he]
  exact hd.deriv
end
end krylov.Envelope
