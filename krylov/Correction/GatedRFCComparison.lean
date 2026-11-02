import krylov.Correction.GatedWindowPhase

/-!
Article: main_krylov, thm:UCq and thm:UCg(iii).
Use: Exact actual gated and ordinary RFC prefix comparison.
Source: proved genuine uniform finite-prefix induction, constructed scalar
allowances and the original real observed correction executor.
-/

namespace krylov.Correction
noncomputable section
open krylov.Methods
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every original measured prefix whose actual spectral tests pass is exactly the ordinary RFC prefix, including all observed records and correction-query traces.
Use: Complete actual uniform ordinary-RFC reasoning without an assumed comparison trajectory.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Induct through the true history executor. The actual accepted spectral decision reduces the genuine correction tree to the ordinary RFC tree, while both methods compute the same real observed-window direction.
-/
theorem gated_actual_passed_prefix_eq_rfc (memory : ℕ → ℕ) (γ : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hgate : ∀ i<N,
      let H := methodRun (gatedMethod memory γ) A B g i
      let W := selectedWindow memory H
      let d := windowDirection W H.gradient
      spectralGate γ ((d,A i d)::W)) :
    ∀ i≤N, methodRun (gatedMethod memory γ) A B g i=methodRun (rfcMethod memory 1) A B g i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hiN : i<N := by omega
    have hprev := ih hiN.le
    have hc : gatedCorrection memory γ (methodRun (gatedMethod memory γ) A B g i)
        (A i ((gatedMethod memory γ).direction (methodRun (gatedMethod memory γ) A B g i)))=
        rfcCorrection memory 1 (methodRun (gatedMethod memory γ) A B g i)
          (A i ((gatedMethod memory γ).direction (methodRun (gatedMethod memory γ) A B g i))) := by
      unfold gatedCorrection
      exact ite_eq_left (hgate i hiN)
    rw [methodRun,methodRun,← hprev]
    unfold methodAdvance
    dsimp only [gatedMethod,rfcMethod,retainedMethod] at hc ⊢
    rw [hc]

end
end krylov.Correction
