import krylov.Methods.RFCSFields
import krylov.Methods.RFCPhase
import krylov.Methods.QuadraticCycles

/-!
Article: main_krylov, thm:RFCS, homogeneous genuine independent-probe cycles.
Use: Derive exact scalar covariance of actual RFC-S gradients, directions,
line steps, full recorded steps and measured secants for arbitrary memory.
Source: the original measured RFC-S executor, fixed retained-age arrays,
proved degree-zero coefficient solves and scale-invariant observed gates.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine independent-probe correction phase is exactly the original fixed-array RFC model phase on its own actual measured secants.
Use: Compare real RFC-S phases in parameter-independent retained-age coordinates.
Article: main_krylov, thm:RFCS, actual homogeneous nonlinear-transfer fields.
Proof: The true recorded pair recursion supplies the retained arrays; rewrite the real correction tree and its two gate branches.
-/
theorem rfcSPhase_array (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    rfcSPhase memory Ap A B g k=rfcArrayPhase
      (fun i : Fin (min (memory k) k) => rfcSStep memory Ap A B g (k-1-i.val))
      (fun i : Fin (min (memory k) k) => rfcSSecant memory Ap A B g (k-1-i.val))
      (rfcSGradient memory Ap A B g k) (rfcSDirection memory Ap A B g k)
      (Ap k (rfcSDirection memory Ap A B g k)) (B k) 1 := by
  unfold rfcSPhase
  dsimp only
  rw [rfcCorrection_array memory 1 _ _ _ k _ _ (rfcSRun_pairs memory Ap A B g k) rfl]
  unfold rfcArrayPhase
  split <;> rfl

/-- Every genuine RFC-S prefix is exactly homogeneous in its initial gradient, including actual line and total steps and all measured secants.
Use: Turn uniform normalized operator-prefix estimates into bounds proportional to the original nonlinear cycle size.
Article: main_krylov, thm:RFCS, actual homogeneous nonlinear-transfer fields.
Proof: Induct over real recorded secants. The actual data direction and finite model phase scale; the genuine probe-to-line mismatch scales with the actual line displacement, so the true next gradient and secant do too.
-/
theorem rfcS_scalar (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E)
    (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    rfcSGradient memory Ap A B (c • g) N=c • rfcSGradient memory Ap A B g N ∧
      ∀ i<N, rfcSDirection memory Ap A B (c • g) i=c • rfcSDirection memory Ap A B g i ∧
        rfcSLineStep memory Ap A B (c • g) i=c • rfcSLineStep memory Ap A B g i ∧
        rfcSStep memory Ap A B (c • g) i=c • rfcSStep memory Ap A B g i ∧
        rfcSSecant memory Ap A B (c • g) i=c • rfcSSecant memory Ap A B g i := by
  induction N with
  | zero => exact ⟨rfl,by intro i hi; omega⟩
  | succ k ih =>
    have hs : (fun i : Fin (min (memory k) k) => rfcSStep memory Ap A B (c • g) (k-1-i.val))=
        fun i => c • rfcSStep memory Ap A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.2.1
    have hy : (fun i : Fin (min (memory k) k) => rfcSSecant memory Ap A B (c • g) (k-1-i.val))=
        fun i => c • rfcSSecant memory Ap A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.2.2
    have hd : rfcSDirection memory Ap A B (c • g) k=c • rfcSDirection memory Ap A B g k := by
      unfold rfcSDirection
      dsimp only
      rw [selectedWindow_of_executed_pairs memory _ _ _ k (rfcSRun_pairs memory Ap A B (c • g) k),
        selectedWindow_of_executed_pairs memory _ _ _ k (rfcSRun_pairs memory Ap A B g k),
        windowDirection_executed_take,windowDirection_executed_take]
      change conjugacyDirection _ _ (rfcSGradient memory Ap A B (c • g) k)=c • conjugacyDirection _ _ (rfcSGradient memory Ap A B g k)
      rw [hs,hy,ih.1,conjugacyDirection_scalar _ _ _ c hc]
    have hl : rfcSLineStep memory Ap A B (c • g) k=c • rfcSLineStep memory Ap A B g k := by
      unfold rfcSLineStep
      dsimp only
      rw [ih.1,hd,map_smul,lineLength_scalar _ _ _ c hc,smul_comm]
    have hp : (rfcSPhase memory Ap A B (c • g) k).movement=c • (rfcSPhase memory Ap A B g k).movement ∧
        (rfcSPhase memory Ap A B (c • g) k).gradient=c • (rfcSPhase memory Ap A B g k).gradient := by
      rw [rfcSPhase_array,rfcSPhase_array,hs,hy,ih.1,hd,map_smul]
      exact rfcArrayPhase_scalar _ _ _ _ _ (B k) 1 c hc
    have hn : rfcSGradient memory Ap A B (c • g) (k+1)=c • rfcSGradient memory Ap A B g (k+1) := by
      rw [rfcSGradient_succ,rfcSGradient_succ,hp.2,hl,map_smul,smul_add]
    have ht : rfcSStep memory Ap A B (c • g) k=c • rfcSStep memory Ap A B g k := by
      rw [rfcSStep,rfcSStep,hl,hp.1,smul_add]
    refine ⟨hn,?_⟩
    intro i hi
    by_cases he : i=k
    · subst i
      refine ⟨hd,hl,ht,?_⟩
      rw [rfcSSecant,rfcSSecant,hn,ih.1,smul_sub]
    · exact ih.2 i (by omega)

/-- Agreement of genuine probe and physical operators before a finite horizon preserves the complete actual RFC-S history through that horizon.
Use: Pack an actual nonlinear operator transcript into the original finite direct operator coordinates.
Article: main_krylov, thm:RFCS, true finite-source operator dictionary.
Proof: Induct on real iterations; the next actual record uses only the current operators and the already common measured prefix.
-/
theorem rfcSRun_congr_prefix (memory : ℕ → ℕ) (Ap A B Cp C D : ℕ → E →L[ℝ] E)
    (g : E) (N : ℕ) (hp : ∀ i<N, Ap i=Cp i) (ha : ∀ i<N, A i=C i) (hb : ∀ i<N, B i=D i) :
    rfcSRun memory Ap A B g N=rfcSRun memory Cp C D g N := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [rfcSRun,rfcSRun,hp k (by omega),ha k (by omega),hb k (by omega),
      ih (fun i hi => hp i (by omega)) (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))]

/-- The genuine RFC-S physical displacement is exactly the finite sum of its actual recorded total steps.
Use: Derive a uniform bound on all real intermediate physical points from the true prefix step estimates.
Article: main_krylov, thm:RFCS, actual homogeneous nonlinear-transfer fields.
Proof: The proved actual measured-pair transcript identifies every recorded step; summing its newest-first recursion gives the same finite chronological sum.
-/
theorem rfcSRun_displacement_sum (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) :
    (rfcSRun memory Ap A B g N).displacement=∑ i∈Finset.range N, rfcSStep memory Ap A B g i := by
  have hp k := rfcSRun_pairs memory Ap A B g k
  have he (k : ℕ) : ((executedPairs (rfcSStep memory Ap A B g) (rfcSSecant memory Ap A B g) k).map Prod.fst).sum=
      ∑ i∈Finset.range k, rfcSStep memory Ap A B g i := by
    induction k with
    | zero => simp only [executedPairs,List.map_nil,List.sum_nil,Finset.sum_range_zero]
    | succ k ih =>
      simp only [executedPairs,List.map_cons,List.sum_cons,Finset.sum_range_succ,ih]
      exact add_comm _ _
  rw [History.displacement,← History.pairs_steps,hp,he]

end
end krylov.Methods
