import krylov.Envelope.VirtualDefectJets
import krylov.Envelope.XRFCFrozenFiltration
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, original explicit virtual injection formula.
Use: identify the actual injection derivative driving the genuine virtual frozen theorem with the printed primitive segment defects on true reference steps and native coefficients.
Source: real primitive XRFC regularity, derived original model domains and genuine zero-defect coefficient action calculus.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine actual virtual injection derivative is exactly the printed original sum of primitive segment derivatives acting on actual stored reference steps with one plus their native coefficients.
Use: The genuine actual virtual injection derivative is exactly the printed original sum of primitive segment derivatives acting on actual stored reference steps with one plus their native coefficients.
Article: main_krylov, thm:E1, original explicit virtual injection formula.
Proof: Derive actual trajectory and native coefficient regularity from primitive trial charts and positive reference models, then differentiate the original executed zero-defect injection sum. -/
theorem xrfc_injection_jet_formula (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (g : E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (hA0 : A 0=fun _ => Q)
    (N : ℕ) (hA : ∀ i,ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A 0) g k)) :
    xrfcInjectionJet trial A Q g N=
      ∑ i : Fin N,(1+oneGradientVirtualCoefficients (xrfcMethod fullMemory trial) (fun _ => Q) g N i) •
        deriv (fun t => A t i.val) 0 (oneGradientStep (xrfcMethod fullMemory trial) (fun _ => Q) g i.val) := by
  let m := xrfcMethod fullMemory trial (E := E)
  -- True primitive trial charts derive every real observation and model coefficient derivative used in the printed injection.
  have hreg := quadraticXRFC_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const Q hA0 hQ hpos N hpre ht hT
  have hdom := (xrfc_full_array_domains trial Q hQ hpos g N hpre ht N le_rfl).2
  have hM : (pairModel
      (fun i : Fin N => oneGradientStep m (A 0) g (N-1-i.val))
      (fun i : Fin N => A 0 (N-1-i.val) (oneGradientStep m (A 0) g (N-1-i.val)))).det≠0 := by
    rw [hA0]
    exact hdom
  exact (virtualInjectionSum_hasDeriv m A Q g N hA0 (fun i _ => (hA i).of_le (by norm_num))
    (fun i hi => (hreg.2 i hi).of_le (by norm_num)) ((hreg.1 N le_rfl).of_le (by norm_num)) hM).deriv
end
end krylov.Envelope
