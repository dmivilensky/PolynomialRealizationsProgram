import krylov.Stability.RetainedPhase
import krylov.Methods.RFCReference

/-!
Article: main_krylov, lem:U(d), joint regularity of actual adaptive RFC trajectories.
Use: derive real gradients, directions, total evaluated steps and recorded
secants from the actual retained-history solves and actual gated correction queries.
Source: the proved actual reference CG model domains, strict observed gates,
fixed finite history coordinates and finite analytic execution induction.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actually executed retained RFC_k prefix is jointly analytic near every nondegenerate positive quadratic reference.
Use: actual trajectory regularity and correction-prefix orders have their genuine model/search/gate domains discharged.
Article: main_krylov, lem:U(d), r=∞ for RFC and repeated RFC.
Proof: induct on real observed iterations. Actual quadratic CG consistency
and positive retained/augmented models justify each finite inverse; actual
positive current curvature justifies exact search. The true observed defect
gate is locally fixed, and the real finite correction-query induction propagates
the actual returned gradient, total step and observed secant to the next iteration. -/
theorem quadraticRFC_prefix_analytic (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i, AnalyticAt ℝ (fun p => A p i) x) (hB : ∀ i, AnalyticAt ℝ (fun p => B p i) x)
    (hg : AnalyticAt ℝ g x) (Q : E →L[ℝ] E) (hAx : A x=(fun _ => Q)) (hBx : B x=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g x) k≠0 → 0<k → 0<memory k) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q (g x) i≠0) :
    AnalyticAt ℝ (fun p => probedGradient (rfcMethod memory count) (A p) (B p) (g p) N) x ∧
      ∀ i<N,
        AnalyticAt ℝ (fun p => (rfcMethod memory count).direction
          (methodRun (rfcMethod memory count) (A p) (B p) (g p) i)) x ∧
        AnalyticAt ℝ (fun p => probedStep (rfcMethod memory count) (A p) (B p) (g p) i) x ∧
        AnalyticAt ℝ (fun p => probedSecant (rfcMethod memory count) (A p) (B p) (g p) i) x := by
  -- Every regularity conclusion below concerns a projection of the genuine nonanticipating method execution.
  induction N with
  | zero => exact ⟨hg,by intro i hi; omega⟩
  | succ k ih =>
    have ht := ih (fun i hi => hpre i (by omega))
    let method := rfcMethod memory count (E := E)
    let H := fun p => methodRun method (A p) (B p) (g p) k
    let s := fun p => probedStep method (A p) (B p) (g p)
    let y := fun p => probedSecant method (A p) (B p) (g p)
    let d := fun p => windowDirection (selectedWindow memory (H p)) (H p).gradient
    let z := fun p => A p k (d p)
    have hp : ∀ i≤k, CG.gradient Q (g x) i≠0 := fun i hi => hpre i (by omega)
    have hdom := rfc_reference_coordinate_domains memory count Q hQ hpos (g x) hm k hp
    have hC : (crossGram (fun i : Fin (min (memory k) k) => y x (k-1-i.val))
        (fun i : Fin (min (memory k) k) => s x (k-1-i.val))).det≠0 := by
      dsimp only [s,y]
      rw [hAx,hBx]
      exact hdom.1
    have hshape (p : X) : (H p).pairs=executedPairs (s p) (y p) k := methodRun_pairs_executed method _ _ _ k
    have hD : AnalyticAt ℝ d x := retained_history_direction_analytic memory H s y x k hshape
      (fun i hi => (ht.2 i hi).2.1) (fun i hi => (ht.2 i hi).2.2) ht.1 hC
    have hZ : AnalyticAt ℝ z x := analytic_operator_apply (hA k) hD
    have hDx : d x=CG.direction Q (g x) k := by
      dsimp only [d,H]
      rw [hAx,hBx]
      exact rfc_reference_direction memory count Q hQ hpos (g x) hm k
    have hZx : z x=Q (CG.direction Q (g x) k) := by dsimp only [z]; rw [hAx,hDx]
    have hcurv : inner ℝ (d x) (z x)≠0 := by
      rw [hDx,hZx]
      exact (hpos _ (CG.invariant_line_pos Q hpos (g x) k
        (CG.invariant Q hQ hpos (g x) k (fun i hi => hp i hi.le)) (hp k le_rfl)).1).ne'
    let α := fun p => lineLength (H p).gradient (d p) (z p)
    have hα : AnalyticAt ℝ α x := (analytic_inner hD ht.1).neg.div (analytic_inner hD hZ) hcurv
    let g' := fun p => searchedGradient (H p).gradient (d p) (z p)
    have hg' : AnalyticAt ℝ g' x := ht.1.add (hα.smul hZ)
    have hmodel : (pairModel
        (Fin.cons (d x) (fun i : Fin (min (memory k) k) => s x (k-1-i.val)))
        (Fin.cons (z x) (fun i : Fin (min (memory k) k) => y x (k-1-i.val)))).det≠0 := by
      dsimp only [s,y]
      rw [hDx,hZx,hAx,hBx]
      exact hdom.2
    have hn (i : Fin (min (memory k) k)) : s x (k-1-i.val)≠0 := by
      have hi := i.isLt
      have hj : k-1-i.val<k := by omega
      dsimp only [s]
      rw [hAx,hBx,(rfc_reference_pair memory count Q hQ hpos (g x) hm _).1]
      obtain ⟨hd,hl,_⟩ := CG.invariant_line_pos Q hpos (g x) (k-1-i.val)
        (CG.invariant Q hQ hpos (g x) (k-1-i.val) (fun j hj' => hpre j (by omega))) (hpre _ (by omega))
      exact smul_ne_zero hl.ne' hd
    have hyQ (i : Fin (min (memory k) k)) : y x (k-1-i.val)=Q (s x (k-1-i.val)) := by
      dsimp only [s,y]
      rw [hAx,hBx,(rfc_reference_pair memory count Q hQ hpos (g x) hm _).1,
        (rfc_reference_pair memory count Q hQ hpos (g x) hm _).2]
    have hphase := retained_history_phase_analytic memory count H s y d z g' (fun p => B p k) x k hshape
      (fun _ => rfl) (fun _ => rfl) (fun i hi => (ht.2 i hi).2.1) (fun i hi => (ht.2 i hi).2.2)
      hD hZ hg' (hB k) hmodel Q hQ hpos hn hyQ
    have hstep : AnalyticAt ℝ (fun p => probedStep method (A p) (B p) (g p) k) x :=
      (hα.smul hD).add hphase.1
    have hsecant : AnalyticAt ℝ (fun p => probedSecant method (A p) (B p) (g p) k) x := hphase.2.sub ht.1
    refine ⟨hphase.2,?_⟩
    intro i hi
    by_cases he : i=k
    · subst i
      exact ⟨hD,hstep,hsecant⟩
    · exact ht.2 i (by omega)

end
end krylov.Stability
