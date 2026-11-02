import krylov.Methods.RFCArray
import krylov.Methods.HomogeneousCorrection

/-!
Article: main_krylov, alg:fc and lem:U(c,d), actual finite RFC phase covariance.
Use: identify the real correction-phase result with one fixed-array formula
and prove its homogeneous scaling through the actual observed gate.
Source: exact real query-coordinate identities and actual coefficient and gate covariance.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real finite RFC correction phase in its actual old-window coefficient coordinates.
Use: both accepted and skipped branches retain their actual returned gradient and actual correction movement.
Article: main_krylov, alg:fc, gated repeated corrections. -/
def rfcArrayPhase {p : ℕ} (S Y : Fin p → E) (g d z : E) (B : E →L[ℝ] E) (count : ℕ) : CorrectionResult E :=
  if 0<p ∧ ‖pairDefect S Y‖<1 then
    let U : Fin (p+1) → E := Fin.cons d S
    let Z : Fin (p+1) → E := Fin.cons z Y
    runCorrections (repeatedModelTree U (pairModel U Z) count (searchedGradient g d z)) B (searchedGradient g d z)
  else ⟨0,searchedGradient g d z,[]⟩

/-- The actual RFC executor returns exactly its fixed-array phase result, with its true observed branch.
Use: algebraic scaling identities refer to real executed gradients and corrections.
Article: main_krylov, alg:fc and lem:U(d).
Proof: the true recorded transcript supplies the actual retained arrays;
rewrite the actual entire correction tree and evaluate its two possible branches. -/
theorem probedRFC_phase_array (memory : ℕ → ℕ) (count : ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let m := rfcMethod memory count (E := E)
    let H := methodRun m A B g k
    probedPhase m A B g k=rfcArrayPhase
      (fun i : Fin (min (memory k) k) => probedStep m A B g (k-1-i.val))
      (fun i : Fin (min (memory k) k) => probedSecant m A B g (k-1-i.val))
      H.gradient (m.direction H) (A k (m.direction H)) (B k) count := by
  let m := rfcMethod memory count (E := E)
  let H := methodRun m A B g k
  change runCorrections (rfcCorrection memory count H (A k (m.direction H))) _ _=_
  rw [rfcCorrection_array memory count H _ _ k _ _ (methodRun_pairs_executed m A B g k) rfl]
  unfold rfcArrayPhase
  split <;> rfl

/-- Actual RFC phase movement and returned gradient are homogeneous of degree one through both observed gate branches.
Use: the same real gated repeated-query phase is used on the entire positive data cone.
Article: main_krylov, lem:U(c,d).
Proof: the genuine normalized defect is scale invariant. On the accepted
branch the actual augmented model scales quadratically and real repeated-query
execution scales linearly; on the skipped branch only the true exact search remains. -/
theorem rfcArrayPhase_scalar {p : ℕ} (S Y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) (count : ℕ) (c : ℝ) (hc : c≠0) :
    (rfcArrayPhase (fun i => c • S i) (fun i => c • Y i) (c • g) (c • d) (c • z) B count).movement=
      c • (rfcArrayPhase S Y g d z B count).movement ∧
    (rfcArrayPhase (fun i => c • S i) (fun i => c • Y i) (c • g) (c • d) (c • z) B count).gradient=
      c • (rfcArrayPhase S Y g d z B count).gradient := by
  -- Fixed finite augmented coordinates make the real gate and every following query directly comparable.
  have hU : (Fin.cons (c • d) (fun i => c • S i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons d S : Fin (p+1) → E) i) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hZ : (Fin.cons (c • z) (fun i => c • Y i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons z Y : Fin (p+1) → E) i) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [rfcArrayPhase,pairDefect_scalar S Y c hc]
  split
  · rw [hU,hZ,pairModel_scalar,searchedGradient_scalar g d z c hc]
    exact repeatedModel_execution_scalar _ _ B count _ c hc
  · simp only [searchedGradient_scalar g d z c hc,smul_zero,and_self]

end
end krylov.Methods
