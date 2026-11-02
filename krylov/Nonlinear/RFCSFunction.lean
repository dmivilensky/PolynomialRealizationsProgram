import krylov.Methods.RFCSFields
import krylov.Methods.QuadraticCycles
import krylov.Nonlinear.GradientExtension

/-!
Article: main_krylov, thm:RFCS, genuine finite-probe nonlinear execution.
Use: Execute RFC-S with real gradient queries and derive its complete
operator transcript from measured finite differences, including zero steps.
Source: Appendix D's predicted-gradient correction rule and the proved
self-adjoint secant representatives for globally Lipschitz gradient error.
-/

namespace krylov.Nonlinear
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One genuine nonlinear RFC-S iteration, with its finite gradient probe and actual evaluated total displacement.
Use: Keep the predicted post-search gradient only inside the model solve; record the true returned gradient and correction observation.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
-/
def rfcSFunctionRecord (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℝ) (H : History E) : IterationRecord E :=
  let x := x₀+H.displacement
  let W := selectedWindow memory H
  let d := windowDirection W H.gradient
  let z := h⁻¹ • (G (x+h • d)-H.gradient)
  let line := lineLength H.gradient d z • d
  let U := (d,z)::W
  if W≠[] ∧ ‖windowDefect W‖<1 then
    let u := combine (windowSteps U) (modelCoefficients (windowSteps U) (windowModel U)
      (searchedGradient H.gradient d z))
    let gnew := G (x+(line+u))
    ⟨d,z,line+u,gnew,[(u,gnew)]⟩
  else
    ⟨d,z,line,G (x+line),[]⟩

/-- The complete nonlinear RFC-S history obtained from genuine finite gradient queries.
Use: Supply the original nonlinear executor before introducing any operator representatives.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
-/
def rfcSFunctionRun (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ) : ℕ → History E
  | 0 => ⟨G x₀,[]⟩
  | k+1 =>
    let H := rfcSFunctionRun memory G x₀ h k
    ⟨H.initial,rfcSFunctionRecord memory G x₀ (h k) H::H.records⟩

/-- The actual physical iterate obtained by summing all recorded nonlinear total steps.
Use: Locate every real probe and evaluated endpoint in the original physical space.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
-/
def rfcSFunctionPoint (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ) (k : ℕ) : E :=
  x₀+(rfcSFunctionRun memory G x₀ h k).displacement

/-- The next recorded gradient is the true gradient at the actual next physical point.
Use: Relate the nonlinear transcript to the original function.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
Proof: Read the genuinely evaluated gradient in each actual defect-gate branch.
-/
theorem rfcSFunctionRecord_gradient (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℝ) (H : History E) :
    (rfcSFunctionRecord memory G x₀ h H).gradient=
      G (x₀+H.displacement+(rfcSFunctionRecord memory G x₀ h H).step) := by
  unfold rfcSFunctionRecord
  dsimp only
  split <;> rfl

/-- Every genuine nonlinear prefix stores the actual gradient at its actual physical iterate.
Use: Identify the current measured data before representing the next real secant.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
Proof: The newest record is an actual gradient query; its total step adds to the exact recorded displacement.
-/
theorem rfcSFunctionRun_gradient (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ) (k : ℕ) :
    (rfcSFunctionRun memory G x₀ h k).gradient=G (rfcSFunctionPoint memory G x₀ h k) := by
  cases k with
  | zero => simp [rfcSFunctionRun,rfcSFunctionPoint,History.displacement,History.gradient]
  | succ k =>
    rw [rfcSFunctionRun]
    change (rfcSFunctionRecord memory G x₀ (h k) (rfcSFunctionRun memory G x₀ h k)).gradient=_
    rw [rfcSFunctionRecord_gradient]
    congr 1
    simp only [rfcSFunctionPoint,rfcSFunctionRun,History.displacement,List.map_cons,List.sum_cons]
    abel

/-- The nonlinear executor uses the true retained-window direction from its own measured history.
Use: Identify its data-only direction with the original operator protocol.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
Proof: Both actual gate branches retain the same genuinely selected direction.
-/
theorem rfcSFunctionRecord_direction (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℝ) (H : History E) :
    (rfcSFunctionRecord memory G x₀ h H).direction=windowDirection (selectedWindow memory H) H.gradient := by
  unfold rfcSFunctionRecord
  dsimp only
  split <;> rfl

/-- The recorded nonlinear probe is exactly the genuine finite difference along the selected actual direction.
Use: Expose the real measured probe without assuming an averaged-operator formula.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
Proof: Both actual gate branches store the same finite gradient difference.
-/
theorem rfcSFunctionRecord_probe (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℝ) (H : History E) :
    (rfcSFunctionRecord memory G x₀ h H).probe=
      h⁻¹ • (G (x₀+H.displacement+h • windowDirection (selectedWindow memory H) H.gradient)-H.gradient) := by
  unfold rfcSFunctionRecord
  dsimp only
  split <;> rfl

/-- Genuine probe and total-step secant actions identify the entire actual nonlinear iteration with the original RFC-S operator iteration.
Use: Transfer the true record, including its real correction observation, to the operator executor.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
Proof: Use the measured probe identity, split the common actual gate, and reconstruct the true gradient from the full total-step secant.
-/
theorem rfcSFunctionRecord_operator (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℝ) (H : History E)
    (Ap A : E →L[ℝ] E)
    (hp : Ap (windowDirection (selectedWindow memory H) H.gradient)=(rfcSFunctionRecord memory G x₀ h H).probe)
    (hs : A (rfcSFunctionRecord memory G x₀ h H).step=(rfcSFunctionRecord memory G x₀ h H).gradient-H.gradient) :
    rfcSAdvance memory Ap A A H=⟨H.initial,rfcSFunctionRecord memory G x₀ h H::H.records⟩ := by
  rw [rfcSFunctionRecord_probe] at hp
  unfold rfcSAdvance
  dsimp only
  rw [hp]
  unfold rfcSFunctionRecord at hs ⊢
  dsimp only at hs ⊢
  split
  · split at hs
    · simp only at hs
      have hg := congrArg (fun w => H.gradient+w) hs
      rw [map_add] at hg
      simp only [add_sub_cancel] at hg
      rw [← hg]
      simp only [add_assoc]
    · contradiction
  · split at hs
    · contradiction
    · simp only at hs
      have hg := congrArg (fun w => H.gradient+w) hs
      simp only [add_sub_cancel] at hg
      rw [← hg]


/-- Actual measured probe and full-step secant identities identify the complete genuine nonlinear prefix with its operator execution.
Use: Apply operator results to a real nonlinear history without assuming trajectory agreement.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
Proof: Induct through the genuine records using the proved one-iteration transcript identity.
-/
theorem rfcSFunctionRun_operator (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ)
    (Ap A : ℕ → E →L[ℝ] E) (N : ℕ)
    (hp : ∀ i<N, Ap i (windowDirection (selectedWindow memory (rfcSFunctionRun memory G x₀ h i))
      (rfcSFunctionRun memory G x₀ h i).gradient)=
      (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).probe)
    (hs : ∀ i<N, A i (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step=
      (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).gradient-
      (rfcSFunctionRun memory G x₀ h i).gradient) :
    rfcSFunctionRun memory G x₀ h N=rfcSRun memory Ap A A (G x₀) N := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [rfcSRun,← ih (fun i hi => hp i (by omega)) (fun i hi => hs i (by omega))]
    exact (rfcSFunctionRecord_operator memory G x₀ (h k) _ (Ap k) (A k)
      (hp k (by omega)) (hs k (by omega))).symm

variable [CompleteSpace E]
open scoped NNReal

/-- Every genuine nonlinear run with globally Lipschitz gradient error has uniformly close self-adjoint probe and segment operators realizing its entire measured transcript.
Use: Construct the operator source from the actual nonlinear requests before proving their localization.
Article: main_krylov, thm:RFCS, actual nonlinear execution and measured operator dictionary.
Proof: Choose the proved self-adjoint representatives of each true finite probe and total-step secant; the exact recorded-gradient invariant then gives complete prefix equality.
-/
theorem rfcSFunctionRun_representatives (memory : ℕ → ℕ) (G : E → E) (x₀ : E)
    (h : ℕ → ℝ) (hh : ∀ i, h i≠0) (Q : E →L[ℝ] E) (hQ : IsSelfAdjoint Q)
    {K : ℝ≥0} (hG : LipschitzWith K (fun x => G x-Q x)) :
    ∃ Ap A : ℕ → E →L[ℝ] E,
      (∀ i, IsSelfAdjoint (Ap i) ∧ ‖Ap i-Q‖≤(K : ℝ) ∧
        IsSelfAdjoint (A i) ∧ ‖A i-Q‖≤(K : ℝ)) ∧
      ∀ N, rfcSFunctionRun memory G x₀ h N=rfcSRun memory Ap A A (G x₀) N := by
  -- Each operator is chosen from an actual query made by the nonlinear executor.
  have hp i := exists_selfAdjoint_probe_of_lipschitz_error G Q hQ hG
    (rfcSFunctionPoint memory G x₀ h i)
    (windowDirection (selectedWindow memory (rfcSFunctionRun memory G x₀ h i))
      (rfcSFunctionRun memory G x₀ h i).gradient) (hh i)
  choose Ap hAp hApbound hApimage using hp
  have hs i := exists_selfAdjoint_secant_of_lipschitz_error G Q hQ hG
    (rfcSFunctionPoint memory G x₀ h i)
    (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step
  choose A hA hAbound hAimage using hs
  refine ⟨Ap,A,fun i => ⟨hAp i,hApbound i,hA i,hAbound i⟩,fun N => ?_⟩
  apply rfcSFunctionRun_operator
  · intro i _
    rw [rfcSFunctionRecord_probe]
    simpa only [rfcSFunctionRun_gradient,rfcSFunctionPoint] using hApimage i
  · intro i _
    rw [rfcSFunctionRecord_gradient,rfcSFunctionRun_gradient]
    exact hAimage i

end
end krylov.Nonlinear
