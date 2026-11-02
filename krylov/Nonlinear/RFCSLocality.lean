import krylov.Nonlinear.RFCSFunction

/-!
Article: main_krylov, thm:RFCS, exact locality of actual nonlinear requests.
Use: Transfer a localized auxiliary gradient run to the original function
by agreement solely at genuine queried points, preserving every real record.
Source: Appendix D's actual finite-probe RFC-S rule and its measured history.
-/

namespace krylov.Nonlinear
noncomputable section
open krylov.Methods
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual next nonlinear iterate is the current physical point plus the genuinely recorded total step.
Use: Locate every evaluated endpoint without imposing a separate trajectory formula.
Article: main_krylov, thm:RFCS, genuine nonlinear localization transfer.
Proof: Collect the true recorded displacement sum and its newest actual step.
-/
theorem rfcSFunctionPoint_succ (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ) (i : ℕ) :
    rfcSFunctionPoint memory G x₀ h (i+1)=rfcSFunctionPoint memory G x₀ h i+
      (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step := by
  simp only [rfcSFunctionPoint,rfcSFunctionRun,History.displacement,List.map_cons,List.sum_cons]
  abel

/-- Agreement at the actual probe and total-step endpoint identifies the entire nonlinear iteration record.
Use: Transfer an auxiliary gradient extension back to the original gradient once its genuine queries are localized.
Article: main_krylov, thm:RFCS, genuine nonlinear localization transfer.
Proof: The probe fixes the common actual gate and computed total step; endpoint agreement then fixes the real gradient and correction trace.
-/
theorem rfcSFunctionRecord_congr (memory : ℕ → ℕ) (G F : E → E) (x₀ : E) (h : ℝ) (H : History E)
    (hp : G (x₀+H.displacement+h • windowDirection (selectedWindow memory H) H.gradient)=
      F (x₀+H.displacement+h • windowDirection (selectedWindow memory H) H.gradient))
    (hs : G (x₀+H.displacement+(rfcSFunctionRecord memory G x₀ h H).step)=
      F (x₀+H.displacement+(rfcSFunctionRecord memory G x₀ h H).step)) :
    rfcSFunctionRecord memory G x₀ h H=rfcSFunctionRecord memory F x₀ h H := by
  unfold rfcSFunctionRecord at hs ⊢
  dsimp only at hs ⊢
  rw [← hp]
  split
  · split at hs
    · simp only at hs
      rw [hs]
    · contradiction
  · split at hs
    · contradiction
    · simp only at hs
      rw [hs]

/-- Agreement at all actually queried nonlinear probes and endpoints identifies the entire genuine finite history.
Use: Prove localization transfer using only queries on the auxiliary trajectory.
Article: main_krylov, thm:RFCS, genuine nonlinear localization transfer.
Proof: Induct on actual records, using the same measured prefix and the proved one-iteration oracle locality.
-/
theorem rfcSFunctionRun_congr (memory : ℕ → ℕ) (G F : E → E) (x₀ : E) (h : ℕ → ℝ) (N : ℕ)
    (h₀ : G x₀=F x₀)
    (hp : ∀ i<N, G (rfcSFunctionPoint memory G x₀ h i+h i • windowDirection
      (selectedWindow memory (rfcSFunctionRun memory G x₀ h i)) (rfcSFunctionRun memory G x₀ h i).gradient)=
      F (rfcSFunctionPoint memory G x₀ h i+h i • windowDirection
      (selectedWindow memory (rfcSFunctionRun memory G x₀ h i)) (rfcSFunctionRun memory G x₀ h i).gradient))
    (hs : ∀ i<N, G (rfcSFunctionPoint memory G x₀ h (i+1))=F (rfcSFunctionPoint memory G x₀ h (i+1))) :
    rfcSFunctionRun memory G x₀ h N=rfcSFunctionRun memory F x₀ h N := by
  induction N with
  | zero => simp only [rfcSFunctionRun,h₀]
  | succ k ih =>
    have hi := ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))
    have hr := rfcSFunctionRecord_congr memory G F x₀ (h k) (rfcSFunctionRun memory G x₀ h k)
      (hp k (by omega)) (by
        have hh := hs k (by omega)
        rw [rfcSFunctionPoint_succ] at hh
        exact hh)
    simp only [rfcSFunctionRun,← hi,← hr]


end
end krylov.Nonlinear
