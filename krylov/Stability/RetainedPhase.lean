import krylov.Stability.RetainedDirection
import krylov.Stability.ObservedGate

/-!
Article: main_krylov, lem:U(d), real gated RFC correction-phase regularity.
Use: propagate the actual analytic observed history through the genuine gate
and all real correction queries in fixed finite coefficient coordinates.
Source: genuine positive quadratic gate continuity, actual model-tree coordinate
invariance and the proved finite observed-gradient analytic induction.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter krylov.Methods krylov.Reference
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual gated RFC correction phase is analytic near a genuine positive quadratic observed history with its true model domain.
Use: empty windows take their real zero-correction branch; nonempty reference gates pass strictly on a proved neighborhood.
Article: main_krylov, lem:U(d), actual gated RFC and repeated RFC regularity.
Proof: coordinate the real observed window by its fixed retained ages. An
empty window is identically empty, while the genuine quadratic defect of a
nonempty window is zero with positive energies, so its real gate stays accepted.
The actual model tree then equals its fixed-coordinate tree, whose real queried
gradients and movements are analytic by the proved finite execution induction. -/
theorem retained_history_phase_analytic (memory : ℕ → ℕ) (count : ℕ)
    (H : X → History E) (s y : X → ℕ → E) (d z g' : X → E) (B : X → E →L[ℝ] E)
    (x : X) (k : ℕ)
    (hshape : ∀ p, (H p).pairs=executedPairs (s p) (y p) k)
    (hdirection : ∀ p, d p=windowDirection (selectedWindow memory (H p)) (H p).gradient)
    (hsearch : ∀ p, g' p=searchedGradient (H p).gradient (d p) (z p))
    (hs : ∀ i<k, AnalyticAt ℝ (fun p => s p i) x)
    (hy : ∀ i<k, AnalyticAt ℝ (fun p => y p i) x)
    (hd : AnalyticAt ℝ d x) (hz : AnalyticAt ℝ z x) (hg' : AnalyticAt ℝ g' x) (hB : AnalyticAt ℝ B x)
    (hmodel : (pairModel
      (Fin.cons (d x) (fun i : Fin (min (memory k) k) => s x (k-1-i.val)))
      (Fin.cons (z x) (fun i : Fin (min (memory k) k) => y x (k-1-i.val)))).det≠0)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hn : ∀ i : Fin (min (memory k) k), s x (k-1-i.val)≠0)
    (hyQ : ∀ i : Fin (min (memory k) k), y x (k-1-i.val)=Q (s x (k-1-i.val))) :
    AnalyticAt ℝ (fun p => (runCorrections (rfcCorrection memory count (H p) (z p)) (B p) (g' p)).movement) x ∧
      AnalyticAt ℝ (fun p => (runCorrections (rfcCorrection memory count (H p) (z p)) (B p) (g' p)).gradient) x := by
  -- Coordinate identities are global equalities of the actual history; only strict gate acceptance is local.
  let S := fun p (i : Fin (min (memory k) k)) => s p (k-1-i.val)
  let Y := fun p (i : Fin (min (memory k) k)) => y p (k-1-i.val)
  have hS (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun p => S p i) x := by
    have hi := i.isLt
    exact hs _ (by omega)
  have hY (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun p => Y p i) x := by
    have hi := i.isLt
    exact hy _ (by omega)
  have hW (p : X) : selectedWindow memory (H p)=
      (executedPairs (s p) (y p) k).take (memory k) :=
    selectedWindow_of_executed_pairs memory (H p) (s p) (y p) k (hshape p)
  by_cases hempty : min (memory k) k=0
  · have hnil (p : X) : selectedWindow memory (H p)=[] := by
      apply List.eq_nil_of_length_eq_zero
      rw [hW,List.length_take,executedPairs_length,hempty]
    have hq (p : X) : rfcCorrection memory count (H p) (z p)=.done := by
      simp only [rfcCorrection,hnil,ne_eq,not_true_eq_false,false_and,ite_false]
    constructor
    · apply (analyticAt_const : AnalyticAt ℝ (fun _ : X => (0 : E)) x).congr
      apply Eventually.of_forall
      intro p
      dsimp only
      rw [hq p]
      rfl
    · apply hg'.congr
      apply Eventually.of_forall
      intro p
      dsimp only
      rw [hq p]
      rfl
  · have hgate := quadratic_pairDefect_gate S Y x (fun i => (hS i).continuousAt)
      (fun i => (hY i).continuousAt) Q hQ hpos hn hyQ
    have hnorm (p : X) : ‖windowDefect (selectedWindow memory (H p))‖=‖pairDefect (S p) (Y p)‖ := by
      rw [hW]
      let W := (executedPairs (s p) (y p) k).take (memory k)
      have hl : W.length=min (memory k) k := by simp only [W,List.length_take,executedPairs_length]
      apply windowDefect_norm_of_coordinates W hl (S p) (Y p)
      · funext i
        exact congrArg Prod.fst (executedPairs_take_get (s p) (y p) k (memory k) i)
      · funext i
        exact congrArg Prod.snd (executedPairs_take_get (s p) (y p) k (memory k) i)
    let U : X → Fin (min (memory k) k+1) → E := fun p => Fin.cons (d p) (S p)
    let Z : X → Fin (min (memory k) k+1) → E := fun p => Fin.cons (z p) (Y p)
    have hU (i : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun p => U p i) x := Fin.cases hd hS i
    have hZ (i : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun p => Z p i) x := Fin.cases hz hY i
    have hC (i j : Fin (min (memory k) k+1)) :
        AnalyticAt ℝ (fun p => pairModel (U p) (Z p) i j) x := analytic_inner (hU _) (hZ _)
    have hphase := repeatedModel_phase_analytic U (fun p => pairModel (U p) (Z p)) B g' x count
      hU hC hB hg' hmodel
    have hq : ∀ᶠ p in 𝓝 x, rfcCorrection memory count (H p) (z p)=
        repeatedModelTree (U p) (pairModel (U p) (Z p)) count (g' p) := by
      filter_upwards [hgate] with p hp
      have hne : selectedWindow memory (H p)≠[] := by
        intro hn'
        have hl := congrArg List.length hn'
        rw [hW,List.length_take,executedPairs_length,List.length_nil] at hl
        exact hempty hl
      have hg : selectedWindow memory (H p)≠[] ∧ ‖windowDefect (selectedWindow memory (H p))‖<1 :=
        ⟨hne,by rw [hnorm]; exact hp⟩
      simp only [rfcCorrection]
      rw [ite_eq_left hg,← hdirection p,← hsearch p,hW]
      have hc := augmentedWindow_coordinates (s p) (y p) k (memory k) (d p) (z p)
      exact repeatedModelTree_window_coordinates _ _ (U p) (Z p) hc.1 hc.2 count (g' p)
    constructor
    · apply hphase.1.congr
      filter_upwards [hq] with p hp
      exact congrArg (fun q => (runCorrections q (B p) (g' p)).movement) hp.symm
    · apply hphase.2.congr
      filter_upwards [hq] with p hp
      exact congrArg (fun q => (runCorrections q (B p) (g' p)).gradient) hp.symm

end
end krylov.Stability
