import krylov.Methods.HomogeneousRFC
import krylov.Correction.GatedExecution
import krylov.Methods.HomogeneousProtocol

/-!
Article: main_krylov, thm:UCq and thm:UCg(iii), complete actual history scaling.
Use: Restore original initial-gradient scales in uniform comparisons while
preserving every true correction query and its actual observed gradient.
Source: genuine finite correction execution, proved nonzero-scale coefficient
and field homogeneity, and exact construction of original iteration records.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full genuine repeated-model correction trace scales every actual queried displacement and every true returned gradient.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Induct over the actual finite query count. The real inverse coefficient and linear oracle identities scale the next query and gradient before the genuine continuation.
-/
theorem repeatedModel_trace_scalar (s : ι → E) (H : Matrix ι ι ℝ)
    (B : E →L[ℝ] E) (count : ℕ) (g : E) (c : ℝ) (hc : c≠0) :
    (runCorrections (repeatedModelTree (fun i => c • s i) ((c*c) • H) count (c • g)) B (c • g)).trace=
      (runCorrections (repeatedModelTree s H count g) B g).trace.map (fun p => (c • p.1,c • p.2)) := by
  induction count generalizing g with
  | zero => rfl
  | succ count ih =>
    simp only [repeatedModelTree,runCorrections,modelCoefficients_scalar s H g c hc,
      combine_scalar,map_smul,← smul_add,List.map_cons]
    rw [ih]

/-- Both original RFC defect-test branches preserve the exact scaled full correction trace.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: The genuine measured defect is invariant, and the actual accepted repeated-model trace scales by its proved finite-query identity; the real fallback trace is empty.
-/
theorem rfcArrayPhase_trace_scalar {p : ℕ} (S Y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) (count : ℕ) (c : ℝ) (hc : c≠0) :
    (rfcArrayPhase (fun i => c • S i) (fun i => c • Y i) (c • g) (c • d) (c • z) B count).trace=
      (rfcArrayPhase S Y g d z B count).trace.map (fun p => (c • p.1,c • p.2)) := by
  have hU : (Fin.cons (c • d) (fun i => c • S i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons d S : Fin (p+1) → E) i) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hZ : (Fin.cons (c • z) (fun i => c • Y i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons z Y : Fin (p+1) → E) i) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  simp only [rfcArrayPhase,pairDefect_scalar S Y c hc]
  split
  · rw [hU,hZ,pairModel_scalar,searchedGradient_scalar g d z c hc]
    exact repeatedModel_trace_scalar _ _ B count _ c hc
  · rfl

/-- Both actual spectral-gated RFC branches preserve the exact scaled correction-query trace.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: The original measured spectral test is invariant under the genuine common pair scale. The accepted true RFC trace has its proved scaling, and the real rejected branch has empty trace.
-/
theorem gatedArrayPhase_trace_scalar {p : ℕ} (γ : ℝ) (S Y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) (c : ℝ) (hc : c≠0) :
    (gatedArrayPhase γ (fun i => c • S i) (fun i => c • Y i) (c • g) (c • d) (c • z) B).trace=
      (gatedArrayPhase γ S Y g d z B).trace.map (fun p => (c • p.1,c • p.2)) := by
  have hU : (Fin.cons (c • d) (fun i => c • S i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons d S : Fin (p+1) → E) i) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hZ : (Fin.cons (c • z) (fun i => c • Y i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons z Y : Fin (p+1) → E) i) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hgate := pairSpectralGate_scalar γ (Fin.cons d S) (Fin.cons z Y) c hc
  simp only [gatedArrayPhase]
  rw [hU,hZ,hgate]
  split
  · exact rfcArrayPhase_trace_scalar S Y g d z B 1 c hc
  · rfl


/-- Genuine per-iteration gradient, direction, step and query-trace scale identities reconstruct exact scaling of the complete actual history.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Induct through the original methodRun records. The true linear oracle scales its current probe, and each actual next record field is its supplied proved real field identity; the complete prior record list scales by induction.
-/
theorem methodRun_scalar_of_true_fields (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (c : ℝ) (N : ℕ)
    (hgradient : ∀ i≤N, probedGradient m A B (c • g) i=c • probedGradient m A B g i)
    (hdirection : ∀ i<N, m.direction (methodRun m A B (c • g) i)=c • m.direction (methodRun m A B g i))
    (hstep : ∀ i<N, probedStep m A B (c • g) i=c • probedStep m A B g i)
    (htrace : ∀ i<N, (probedPhase m A B (c • g) i).trace=
      (probedPhase m A B g i).trace.map (fun p => (c • p.1,c • p.2))) :
    methodRun m A B (c • g) N=scaleHistory c (methodRun m A B g N) := by
  have hpref : ∀ k≤N, methodRun m A B (c • g) k=scaleHistory c (methodRun m A B g k) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hkN : k<N := by omega
      have hprev := ih hkN.le
      change (⟨(methodRun m A B (c • g) k).initial,
        ⟨m.direction (methodRun m A B (c • g) k),A k (m.direction (methodRun m A B (c • g) k)),
          probedStep m A B (c • g) k,probedGradient m A B (c • g) (k+1),(probedPhase m A B (c • g) k).trace⟩::
          (methodRun m A B (c • g) k).records⟩ : History E)=
        scaleHistory c (⟨(methodRun m A B g k).initial,
          ⟨m.direction (methodRun m A B g k),A k (m.direction (methodRun m A B g k)),
            probedStep m A B g k,probedGradient m A B g (k+1),(probedPhase m A B g k).trace⟩::
            (methodRun m A B g k).records⟩ : History E)
      rw [hdirection k hkN,map_smul,hstep k hkN,hgradient (k+1) hk,htrace k hkN]
      rw [hprev]
      rfl
  exact hpref N le_rfl


/-- Every original repeated RFC iteration has its exact scaled real query trace.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: The proved actual field homogeneity identifies every retained old step, measured secant, current gradient, direction and probe in the genuine finite-array execution dictionary. Apply the true RFC phase trace law.
-/
theorem rfc_actual_trace_scalar (memory : ℕ → ℕ) (count : ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (k : ℕ) :
    let m := rfcMethod memory count (E := E)
    (probedPhase m A B (c • g) k).trace=
      (probedPhase m A B g k).trace.map (fun p => (c • p.1,c • p.2)) := by
  let m := rfcMethod memory count (E := E)
  have hs := rfc_scalar memory count A B g c hc (k+1)
  have hstep (j : Fin (min (memory k) k)) : probedStep m A B (c • g) (k-1-j.val)=c • probedStep m A B g (k-1-j.val) :=
    ((hs.2 _ (by omega)).2).1
  have hsecant (j : Fin (min (memory k) k)) : probedSecant m A B (c • g) (k-1-j.val)=c • probedSecant m A B g (k-1-j.val) :=
    ((hs.2 _ (by omega)).2).2
  have hS : (fun j : Fin (min (memory k) k) => probedStep m A B (c • g) (k-1-j.val))=
      fun j => c • probedStep m A B g (k-1-j.val) := funext hstep
  have hY : (fun j : Fin (min (memory k) k) => probedSecant m A B (c • g) (k-1-j.val))=
      fun j => c • probedSecant m A B g (k-1-j.val) := funext hsecant
  have hg : (methodRun m A B (c • g) k).gradient=c • (methodRun m A B g k).gradient :=
    (rfc_scalar memory count A B g c hc k).1
  have hd : m.direction (methodRun m A B (c • g) k)=c • m.direction (methodRun m A B g k) :=
    (hs.2 k (Nat.lt_succ_self k)).1
  dsimp only
  rw [probedRFC_phase_array memory count A B (c • g) k,probedRFC_phase_array memory count A B g k]
  rw [hS,hY,hg,hd,map_smul]
  exact rfcArrayPhase_trace_scalar _ _ _ _ _ (B k) count c hc

/-- Every original repeated RFC run scales its complete actual measured history under any nonzero common initial-gradient scale.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Combine the proved genuine field and full-query-trace scaling identities in the exact actual-record reconstruction theorem.
-/
theorem rfc_complete_history_scalar (memory : ℕ → ℕ) (count : ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    methodRun (rfcMethod memory count) A B (c • g) N=scaleHistory c (methodRun (rfcMethod memory count) A B g N) := by
  apply methodRun_scalar_of_true_fields (rfcMethod memory count) A B g c N
  · intro i _hi
    exact (rfc_scalar memory count A B g c hc i).1
  · intro i hi
    exact ((rfc_scalar memory count A B g c hc N).2 i hi).1
  · intro i hi
    exact ((rfc_scalar memory count A B g c hc N).2 i hi).2.1
  · intro i _hi
    exact rfc_actual_trace_scalar memory count A B g c hc i


/-- Every original gated RFC iteration has its exact scaled real query trace.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Actual trajectory field homogeneity identifies the genuine retained array, current direction and original probe at both scales. Apply the proved actual gated phase trace law through both real tests.
-/
theorem gated_actual_trace_scalar (memory : ℕ → ℕ) (γ : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (k : ℕ) :
    let m := gatedMethod memory γ (E := E)
    (probedPhase m A B (c • g) k).trace=
      (probedPhase m A B g k).trace.map (fun p => (c • p.1,c • p.2)) := by
  let m := gatedMethod memory γ (E := E)
  have hs := gated_scalar memory γ A B g c hc (k+1)
  have hstep (j : Fin (min (memory k) k)) : probedStep m A B (c • g) (k-1-j.val)=c • probedStep m A B g (k-1-j.val) :=
    ((hs.2 _ (by omega)).2).1
  have hsecant (j : Fin (min (memory k) k)) : probedSecant m A B (c • g) (k-1-j.val)=c • probedSecant m A B g (k-1-j.val) :=
    ((hs.2 _ (by omega)).2).2
  have hS : (fun j : Fin (min (memory k) k) => probedStep m A B (c • g) (k-1-j.val))=
      fun j => c • probedStep m A B g (k-1-j.val) := funext hstep
  have hY : (fun j : Fin (min (memory k) k) => probedSecant m A B (c • g) (k-1-j.val))=
      fun j => c • probedSecant m A B g (k-1-j.val) := funext hsecant
  have hg : (methodRun m A B (c • g) k).gradient=c • (methodRun m A B g k).gradient :=
    (gated_scalar memory γ A B g c hc k).1
  have hd : m.direction (methodRun m A B (c • g) k)=c • m.direction (methodRun m A B g k) :=
    (hs.2 k (Nat.lt_succ_self k)).1
  dsimp only
  rw [probedGated_phase_array memory γ A B (c • g) k,probedGated_phase_array memory γ A B g k]
  rw [hS,hY,hg,hd,map_smul]
  exact gatedArrayPhase_trace_scalar γ _ _ _ _ _ (B k) c hc

/-- Every original gated RFC run scales its complete real measured history under any nonzero initial-gradient scale.
Use: Remove normalization in original uniform RFC and gated-RFC statements.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: The genuine gradient, direction, total-step and full-query-trace homogeneity reconstructs every actual scaled iteration record and its true prior history.
-/
theorem gated_complete_history_scalar (memory : ℕ → ℕ) (γ : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    methodRun (gatedMethod memory γ) A B (c • g) N=scaleHistory c (methodRun (gatedMethod memory γ) A B g N) := by
  apply methodRun_scalar_of_true_fields (gatedMethod memory γ) A B g c N
  · intro i _hi
    exact (gated_scalar memory γ A B g c hc i).1
  · intro i hi
    exact ((gated_scalar memory γ A B g c hc N).2 i hi).1
  · intro i hi
    exact ((gated_scalar memory γ A B g c hc N).2 i hi).2.1
  · intro i _hi
    exact gated_actual_trace_scalar memory γ A B g c hc i

end
end krylov.Correction
