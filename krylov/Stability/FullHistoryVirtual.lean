import krylov.Stability.ContDiffWindows
import krylov.Cancellation.DCEstimateRegularity
set_option autoImplicit false
/-!
Article: Lemma B.1 [lem:U] of krylov.tex.
Use: derive actual virtual correction, gradient and direction regularity for
history-only policies from the two genuine observed inverse domains.
Source: real fixed-shape history getters and the proved finite-window calculus. -/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Cancellation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Complete observed-history virtual corrections, gradients and directions
are C-r at their two actual reference inverse domains.
Use: smooth scalar policies can share the true primitive observed calculus
without assuming any executed trajectory or virtual solve is smooth.
Article: main_krylov, lem:U(d).
Proof: fixed-shape reconstruction gives genuinely smooth recorded getters
and current gradients. The true complete observed list reconstructs the
actual reference history; apply the existing finite-window virtual calculus. -/
theorem full_history_virtual_contDiffAt (H : History E) (r : WithTop ℕ∞)
    (hM : (windowModel H.pairs).det≠0)
    (hC : (crossGram (windowImages H.pairs) (windowSteps H.pairs)).det≠0) :
    let shape := H.queryShape
    let m := H.observationList.length
    let x := observedArray m H.observationList
    let W := fun z : Fin m → E => (historyFromObservations shape (List.ofFn z)).pairs
    let G := fun z : Fin m → E => (historyFromObservations shape (List.ofFn z)).gradient
    ContDiffAt ℝ r (fun z => virtualCorrection (W z) (G z)) x ∧
      ContDiffAt ℝ r (fun z => virtualGradient (W z) (G z)) x ∧
      ContDiffAt ℝ r (fun z => windowDirection (W z) (virtualGradient (W z) (G z))) x := by
  let shape := H.queryShape
  let m := H.observationList.length
  let x := observedArray m H.observationList
  let W := fun z : Fin m → E => chartWindow fullMemory shape z
  let G := fun z : Fin m → E => chartGradient shape z
  have hW : W x=H.pairs := by
    dsimp only [W,chartWindow,shape,x,m]
    rw [ofFn_observedArray,historyFromObservations_actual,selectedWindow_full]
  have hs := chartSteps_regular fullMemory shape (fun z : Fin m → E => z) x (r := r) contDiffAt_id
  have hg := (chartWindow_regular fullMemory shape (fun z : Fin m → E => z) x (r := r) contDiffAt_id).2
  have hb := contDiff_windowBlock W (fun z => chartWindow_length fullMemory shape z) G x
    (fun i => (hs i).1) (fun i => (hs i).2) hg
    (by rw [hW];exact hM) (by rw [hW];exact hC)
  have he (z : Fin m → E) : W z=(historyFromObservations shape (List.ofFn z)).pairs := selectedWindow_full _
  constructor
  · apply hb.1.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z =>
      congrArg (fun W => virtualCorrection W (G z)) (he z).symm)
  · constructor
    · apply hb.2.1.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun z =>
        congrArg (fun W => virtualGradient W (G z)) (he z).symm)
    · apply hb.2.2.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun z =>
        congrArg (fun W => windowDirection W (virtualGradient W (G z))) (he z).symm)

end
end krylov.Stability
