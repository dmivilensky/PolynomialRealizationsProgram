import krylov.Methods.RFCSFields
import krylov.Stability.AnalyticRFC

/-!
Article: main_krylov, thm:RFCS, actual secant-probed RFC execution.
Use: distinguish the measured probe from the real line and correction
segments throughout the genuine observed history and final residual.
Source: the actual RFC-S executor, real retained finite pair arrays and
proved positive-quadratic model/search/gate domains.
-/


namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine independent-probe RFC-S prefix is jointly analytic near every actual full positive quadratic reference, with all real measured fields derived from primitive operator regularity.
Use: the final only-last-probe expansion has genuine trajectory regularity and actual search/model/gate domains, rather than an assumed smooth run.
Article: main_krylov, thm:RFCS, true independent-probe prefix regularity.
Proof: induct on actual recorded steps and evaluated secants. Genuine
quadratic RFC-S execution supplies the positive original reference domains.
The existing retained-history direction and correction-phase theorems apply
to its true measured arrays. Analytic predicted search and the exact real
probe-to-line mismatch identity propagate the actual next gradient, total
evaluated step and measured secant through the genuine independent-probe run. -/
theorem quadraticRFCS_prefix_analytic (memory : ℕ → ℕ)
    (Ap A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hAp : ∀ i, AnalyticAt ℝ (fun p => Ap p i) x)
    (hA : ∀ i, AnalyticAt ℝ (fun p => A p i) x) (hB : ∀ i, AnalyticAt ℝ (fun p => B p i) x)
    (hg : AnalyticAt ℝ g x) (Q : E →L[ℝ] E) (hApx : Ap x=(fun _ => Q))
    (hAx : A x=(fun _ => Q)) (hBx : B x=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g x) k≠0 → 0<k → 0<memory k) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q (g x) i≠0) :
    AnalyticAt ℝ (fun p => rfcSGradient memory (Ap p) (A p) (B p) (g p) N) x ∧
      ∀ i<N,
        AnalyticAt ℝ (fun p => rfcSDirection memory (Ap p) (A p) (B p) (g p) i) x ∧
        AnalyticAt ℝ (fun p => rfcSStep memory (Ap p) (A p) (B p) (g p) i) x ∧
        AnalyticAt ℝ (fun p => rfcSSecant memory (Ap p) (A p) (B p) (g p) i) x := by
  -- Keep the genuine independent probe and actual physical segment operators throughout the execution induction.
  induction N with
  | zero => exact ⟨hg,by intro i hi; omega⟩
  | succ k ih =>
    have ht := ih (fun i hi => hpre i (by omega))
    let H := fun p => rfcSRun memory (Ap p) (A p) (B p) (g p) k
    let s := fun p => rfcSStep memory (Ap p) (A p) (B p) (g p)
    let y := fun p => rfcSSecant memory (Ap p) (A p) (B p) (g p)
    let d := fun p => rfcSDirection memory (Ap p) (A p) (B p) (g p) k
    let z := fun p => Ap p k (d p)
    have hp : ∀ i≤k, CG.gradient Q (g x) i≠0 := fun i hi => hpre i (by omega)
    have hdom := rfc_reference_coordinate_domains memory 1 Q hQ hpos (g x) hm k hp
    have hC : (crossGram (fun i : Fin (min (memory k) k) => y x (k-1-i.val))
        (fun i : Fin (min (memory k) k) => s x (k-1-i.val))).det≠0 := by
      dsimp only [s,y]
      simp only [hApx,hAx,hBx,(rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) _).2.2.1,
        (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) _).2.2.2]
      exact hdom.1
    have hshape (p : X) : (H p).pairs=executedPairs (s p) (y p) k := rfcSRun_pairs memory _ _ _ _ k
    have hD : AnalyticAt ℝ d x := retained_history_direction_analytic memory H s y x k hshape
      (fun i hi => (ht.2 i hi).2.1) (fun i hi => (ht.2 i hi).2.2) ht.1 hC
    have hZ : AnalyticAt ℝ z x := analytic_operator_apply (hAp k) hD
    have hDx : d x=CG.direction Q (g x) k := by
      dsimp only [d]
      rw [hApx,hAx,hBx,(rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) k).2.1]
      exact rfc_reference_direction memory 1 Q hQ hpos (g x) hm k
    have hZx : z x=Q (CG.direction Q (g x) k) := by dsimp only [z]; rw [hApx,hDx]
    have hcurv : inner ℝ (d x) (z x)≠0 := by
      rw [hDx,hZx]
      exact (hpos _ (CG.invariant_line_pos Q hpos (g x) k
        (CG.invariant Q hQ hpos (g x) k (fun i hi => hp i hi.le)) (hp k le_rfl)).1).ne'
    let α := fun p => lineLength (H p).gradient (d p) (z p)
    have hα : AnalyticAt ℝ α x := (analytic_inner hD ht.1).neg.div (analytic_inner hD hZ) hcurv
    let gp := fun p => searchedGradient (H p).gradient (d p) (z p)
    have hgp : AnalyticAt ℝ gp x := ht.1.add (hα.smul hZ)
    have hmodel : (pairModel
        (Fin.cons (d x) (fun i : Fin (min (memory k) k) => s x (k-1-i.val)))
        (Fin.cons (z x) (fun i : Fin (min (memory k) k) => y x (k-1-i.val)))).det≠0 := by
      dsimp only [s,y]
      simp only [hDx,hZx,hApx,hAx,hBx,(rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) _).2.2.1,
        (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) _).2.2.2]
      exact hdom.2
    have hn (i : Fin (min (memory k) k)) : s x (k-1-i.val)≠0 := by
      have hi := i.isLt
      dsimp only [s]
      rw [hApx,hAx,hBx,(rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) _).2.2.1,
        (rfc_reference_pair memory 1 Q hQ hpos (g x) hm _).1]
      obtain ⟨hd,hl,_⟩ := CG.invariant_line_pos Q hpos (g x) (k-1-i.val)
        (CG.invariant Q hQ hpos (g x) (k-1-i.val) (fun j hj => hpre j (by omega))) (hpre _ (by omega))
      exact smul_ne_zero hl.ne' hd
    have hyQ (i : Fin (min (memory k) k)) : y x (k-1-i.val)=Q (s x (k-1-i.val)) := by
      dsimp only [s,y]
      rw [hApx,hAx,hBx,(rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) _).2.2.1,
        (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g x) _).2.2.2,
        (rfc_reference_pair memory 1 Q hQ hpos (g x) hm _).1,
        (rfc_reference_pair memory 1 Q hQ hpos (g x) hm _).2]
    have hphase := retained_history_phase_analytic memory 1 H s y d z gp (fun p => B p k) x k hshape
      (fun _ => rfl) (fun _ => rfl) (fun i hi => (ht.2 i hi).2.1) (fun i hi => (ht.2 i hi).2.2)
      hD hZ hgp (hB k) hmodel Q hQ hpos hn hyQ
    have hstep : AnalyticAt ℝ (fun p => rfcSStep memory (Ap p) (A p) (B p) (g p) k) x :=
      (hα.smul hD).add hphase.1
    -- Restore the physically evaluated gradient from the predicted correction and actual line mismatch.
    have hnext : AnalyticAt ℝ (fun p => rfcSGradient memory (Ap p) (A p) (B p) (g p) (k+1)) x := by
      have hactual := hphase.2.add (analytic_operator_apply ((hA k).sub (hAp k)) (hα.smul hD))
      apply hactual.congr
      exact Filter.Eventually.of_forall fun p => (rfcSGradient_succ memory _ _ _ _ k).symm
    have hsecant : AnalyticAt ℝ (fun p => rfcSSecant memory (Ap p) (A p) (B p) (g p) k) x := hnext.sub ht.1
    refine ⟨hnext,?_⟩
    intro i hi
    by_cases he : i=k
    · subst i
      exact ⟨hD,hstep,hsecant⟩
    · exact ht.2 i (by omega)

end
end krylov.Stability
