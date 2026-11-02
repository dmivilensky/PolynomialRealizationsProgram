import krylov.Correction.GatedRFCComparison
import krylov.Correction.GatedUniformCutoff

/-!
Article: main_krylov, thm:UCg(iii), actual arbitrary-threshold comparison.
Use: Preserve the ordinary nonstagnation constant while shrinking only the
actual source radius for a requested measured spectral-gate threshold.
Source: true Hermitian Rayleigh conditioning, actual column-normalized
model algebra and the genuine full observed correction executor.
-/

namespace krylov.Correction
noncomputable section
open krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}

/-- Every genuinely defined gated cycle whose ordinary active-direction spectral tests pass has exactly the ordinary full measured history.
Use: Transfer the real uniform ordinary-RFC conclusions to the original gated method.
Article: main_krylov, thm:UCg(iii).
Proof: Induct over the original executor. The actual defined gated curvature makes its current direction nonzero; the already equal complete histories give the same nonzero ordinary direction. Its proved actual spectral decision reduces the real gated correction tree to the ordinary tree, preserving the entire next record and correction-query trace.
-/
theorem gated_defined_cycle_eq_rfc_of_active_gates (γ : ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hdefined : gatedFullRunDefined γ A B g N)
    (hgate : ∀ i<N,
      let H := methodRun (rfcMethod fullMemory 1) A B g i
      let W := selectedWindow fullMemory H
      let d := windowDirection W H.gradient
      d≠0 → spectralGate γ ((d,A i d)::W)) :
    ∀ i≤N, methodRun (gatedMethod fullMemory γ) A B g i=methodRun (rfcMethod fullMemory 1) A B g i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hiN : i<N := by omega
    have hprev := ih hiN.le
    have hd : (gatedMethod fullMemory γ).direction (methodRun (gatedMethod fullMemory γ) A B g i)≠0 := by
      intro hz
      have hc := (hdefined i hiN).2
      rw [hz,map_zero,inner_zero_left] at hc
      exact hc rfl
    have hd' : (rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g i)≠0 := by
      rw [hprev] at hd
      exact hd
    have hpassed := hgate i hiN hd'
    rw [← hprev] at hpassed
    have hc : gatedCorrection fullMemory γ (methodRun (gatedMethod fullMemory γ) A B g i)
        (A i ((gatedMethod fullMemory γ).direction (methodRun (gatedMethod fullMemory γ) A B g i)))=
        rfcCorrection fullMemory 1 (methodRun (gatedMethod fullMemory γ) A B g i)
          (A i ((gatedMethod fullMemory γ).direction (methodRun (gatedMethod fullMemory γ) A B g i))) := by
      unfold gatedCorrection
      exact ite_eq_left hpassed
    rw [methodRun,methodRun,← hprev]
    unfold methodAdvance
    dsimp only [gatedMethod,rfcMethod,retainedMethod] at hc ⊢
    rw [hc]

end
end krylov.Correction
