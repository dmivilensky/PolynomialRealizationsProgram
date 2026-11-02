import krylov.Correction.GateScaling
import krylov.Methods.HomogeneousRFC

/-!
Article: main_krylov, def:GRFC, covariance of the actual gated execution.
Use: transport the proved observed spectral tests through the real method,
including the FC fallback and all true recorded step/secant pairs.
Source: genuine finite retained-window coordinates, exact spectral gate
covariance and the existing actual RFC phase and exact-search scaling laws.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A pure finite length cast leaves the actual measured spectral decision unchanged.
Use: the list policy and fixed chronological-age arrays have the same gate.
Article: main_krylov, def:GRFC, actual finite observed spectral test.
Proof: equality elimination makes both coordinate casts the identity. -/
theorem matrixSpectralGate_finCongr {a b : ℕ} (h : a=b) (gamma : ℝ)
    (H : Matrix (Fin b) (Fin b) ℝ) :
    matrixSpectralGate gamma (H.submatrix (finCongr h) (finCongr h)) ↔ matrixSpectralGate gamma H := by
  subst b
  rfl

/-- The genuine list spectral test equals its actual fixed-coordinate pair-model test.
Use: discharge all list-length casts before comparing executed gate branches.
Article: main_krylov, def:GRFC, chronological observed test.
Proof: identify the real list model under its pure coordinate cast and
apply the proved finite-cast invariance of the actual spectral predicate. -/
theorem spectralGate_coordinates (W : List (E × E)) {b : ℕ} (h : W.length=b)
    (s y : Fin b → E) (hs : windowSteps W=s ∘ finCongr h) (hy : windowImages W=y ∘ finCongr h)
    (gamma : ℝ) : spectralGate gamma W ↔ matrixSpectralGate gamma (pairModel s y) := by
  rw [← matrixSpectralGate_window,windowModel_of_coordinates W h s y hs hy]
  exact matrixSpectralGate_finCongr h gamma _

/-- The actual gated one-correction phase in its true fixed retained coordinates.
Use: both spectral rejection and ordinary RFC rejection retain their true FC result.
Article: main_krylov, def:GRFC, executed accepted and fallback phases. -/
def gatedArrayPhase {p : ℕ} (gamma : ℝ) (S Y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) : CorrectionResult E := by
  classical
  exact if matrixSpectralGate gamma (pairModel (Fin.cons d S) (Fin.cons z Y)) then
    rfcArrayPhase S Y g d z B 1 else ⟨0,searchedGradient g d z,[]⟩

/-- The actual gated executor is exactly its fixed-array phase, including both genuine gate decisions.
Use: subsequent scaling assertions concern the real returned gradient and recorded movement.
Article: main_krylov, def:GRFC, fixed-coordinate actual execution.
Proof: use the true retained pairs of the gated run itself. Their augmented
finite coordinates identify the spectral test, and the existing general
RFC tree-coordinate theorem identifies the accepted real correction phase. -/
theorem probedGated_phase_array (memory : ℕ → ℕ) (gamma : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let m := gatedMethod memory gamma (E := E)
    let H := methodRun m A B g k
    probedPhase m A B g k=gatedArrayPhase gamma
      (fun i : Fin (min (memory k) k) => probedStep m A B g (k-1-i.val))
      (fun i : Fin (min (memory k) k) => probedSecant m A B g (k-1-i.val))
      H.gradient (m.direction H) (A k (m.direction H)) (B k) := by
  classical
  -- Use the gated method's own actual history; an ordinary RFC comparison history is unnecessary.
  let m := gatedMethod memory gamma (E := E)
  let H := methodRun m A B g k
  let d := m.direction H
  let z := A k d
  let s := probedStep m A B g
  let y := probedSecant m A B g
  have hw : selectedWindow memory H=(executedPairs s y k).take (memory k) :=
    selectedWindow_methodRun memory m A B g k
  have hg := augmentedWindow_coordinates s y k (memory k) d z
  have hgate := spectralGate_coordinates ((d,z)::(executedPairs s y k).take (memory k))
    (by simp only [List.length_cons,List.length_take,executedPairs_length])
    (Fin.cons d (fun i : Fin (min (memory k) k) => s (k-1-i.val)))
    (Fin.cons z (fun i : Fin (min (memory k) k) => y (k-1-i.val))) hg.1 hg.2 gamma
  change runCorrections (gatedCorrection memory gamma H z) (B k)
    (searchedGradient H.gradient d z)=_
  unfold gatedCorrection
  dsimp only
  change runCorrections (if spectralGate gamma ((d,z)::selectedWindow memory H) then
    rfcCorrection memory 1 H z else .done) (B k) (searchedGradient H.gradient d z)=_
  rw [hw,hgate]
  unfold gatedArrayPhase
  split
  · rw [rfcCorrection_array memory 1 H s y k d z (methodRun_pairs_executed m A B g k) rfl]
    unfold rfcArrayPhase
    split <;> rfl
  · rfl

/-- The actual gated phase scales with every nonzero common initial-data scale.
Use: the spectral and defect tests choose the same genuine branches at every scale.
Article: main_krylov, def:GRFC, g₀↦λg₀ phase covariance.
Proof: the augmented pair model scales by λ² and its actual spectral test
is invariant; the accepted real RFC phase has the proved scalar covariance,
while the fallback is the genuine homogeneous exact-search result. -/
theorem gatedArrayPhase_scalar {p : ℕ} (gamma : ℝ) (S Y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) (c : ℝ) (hc : c≠0) :
    (gatedArrayPhase gamma (fun i => c • S i) (fun i => c • Y i)
      (c • g) (c • d) (c • z) B).movement=c • (gatedArrayPhase gamma S Y g d z B).movement ∧
    (gatedArrayPhase gamma (fun i => c • S i) (fun i => c • Y i)
      (c • g) (c • d) (c • z) B).gradient=c • (gatedArrayPhase gamma S Y g d z B).gradient := by
  -- Cancel the same real data scale in both actual observed tests before entering either branch.
  have hu : (Fin.cons (c • d) (fun i => c • S i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons d S : Fin (p+1) → E) i) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hz : (Fin.cons (c • z) (fun i => c • Y i) : Fin (p+1) → E)=
      fun i => c • ((Fin.cons z Y : Fin (p+1) → E) i) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hgate := pairSpectralGate_scalar gamma (Fin.cons d S) (Fin.cons z Y) c hc
  simp only [gatedArrayPhase]
  rw [hu,hz,hgate]
  split
  · exact rfcArrayPhase_scalar S Y g d z B 1 c hc
  · simp only [searchedGradient_scalar g d z c hc,smul_zero,and_self]

/-- Every actual GRFC run scales its returned gradient, directions, total steps and recorded secants by any nonzero common initial-data scale.
Use: transport the source scaling law through the entire genuine executed trajectory, for every memory rule and every fallback branch.
Article: main_krylov, def:GRFC, full g₀↦λg₀ covariance.
Proof: induct on the true recorded step/secant data. The actual retained
direction scales by the existing inverse-coefficient identity; the real
spectral-gated phase scales by the preceding theorem. The actual exact line
step and correction movement therefore scale together, as do the next true
gradient and its recorded consecutive-gradient secant. -/
theorem gated_scalar (memory : ℕ → ℕ) (gamma : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    let m := gatedMethod memory gamma (E := E)
    probedGradient m A B (c • g) N=c • probedGradient m A B g N ∧
      ∀ i<N, m.direction (methodRun m A B (c • g) i)=c • m.direction (methodRun m A B g i) ∧
        probedStep m A B (c • g) i=c • probedStep m A B g i ∧
        probedSecant m A B (c • g) i=c • probedSecant m A B g i := by
  -- The real recorded secants remain part of the induction through accepted and skipped corrections.
  let m := gatedMethod memory gamma (E := E)
  change probedGradient m A B (c • g) N=c • probedGradient m A B g N ∧ _
  induction N with
  | zero => exact ⟨rfl,by intro i hi; omega⟩
  | succ k ih =>
    have hs : (fun i : Fin (min (memory k) k) => probedStep m A B (c • g) (k-1-i.val))=
        fun i => c • probedStep m A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.1
    have hy : (fun i : Fin (min (memory k) k) => probedSecant m A B (c • g) (k-1-i.val))=
        fun i => c • probedSecant m A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.2
    have hd : m.direction (methodRun m A B (c • g) k)=c • m.direction (methodRun m A B g k) := by
      change windowDirection (selectedWindow memory _) _=c • windowDirection (selectedWindow memory _) _
      rw [selectedWindow_methodRun,selectedWindow_methodRun,windowDirection_executed_take,windowDirection_executed_take]
      change conjugacyDirection _ _ (probedGradient m A B (c • g) k)=c • conjugacyDirection _ _ (probedGradient m A B g k)
      rw [hs,hy,ih.1,conjugacyDirection_scalar _ _ _ c hc]
    have hphase : (probedPhase m A B (c • g) k).movement=c • (probedPhase m A B g k).movement ∧
        (probedPhase m A B (c • g) k).gradient=c • (probedPhase m A B g k).gradient := by
      simp only [m,probedGated_phase_array]
      change (gatedArrayPhase _ _ _ (probedGradient m A B (c • g) k) _ _ _).movement=_ ∧
        (gatedArrayPhase _ _ _ (probedGradient m A B (c • g) k) _ _ _).gradient=_
      rw [hs,hy,ih.1,hd,map_smul]
      exact gatedArrayPhase_scalar gamma _ _ _ _ _ (B k) c hc
    have hnext : probedGradient m A B (c • g) (k+1)=c • probedGradient m A B g (k+1) := hphase.2
    have hstep : probedStep m A B (c • g) k=c • probedStep m A B g k := by
      change lineLength (probedGradient m A B (c • g) k) _ _ • _+_=c • _
      rw [ih.1,hd,map_smul,lineLength_scalar _ _ _ c hc,hphase.1,smul_comm,← smul_add]
      rfl
    refine ⟨hnext,?_⟩
    intro i hi
    by_cases he : i=k
    · subst i
      refine ⟨hd,hstep,?_⟩
      rw [probedSecant,hnext,ih.1,← smul_sub]
      rfl
    · exact ih.2 i (by omega)

end
end krylov.Correction
