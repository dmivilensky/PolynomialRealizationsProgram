import krylov.Stability.RFCProjectedOrders
import krylov.Stability.RecordedProjectionOrder

/-!
Article: main_krylov, lem:projected-residual, actual recorded RFC window orders.
Use: carry the proved actual repeated augmented residual estimate to the
genuine total recorded step and actual old retained steps.
Source: actual RFC analytic execution, genuine reference compressed/Gram
domains and actual executed-step span membership.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference
open scoped Topology InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual repeated RFC recorded old-plus-new window has its projected-residual order c+1 on every noninitial nondegenerate prefix.
Use: the source S_(k+1)ᵀg_(k+1) order concerns the genuine total recorded step, with all coordinate/spanning premises discharged.
Article: main_krylov, lem:projected-residual, actual recorded RFC_k prefix order.
Proof: true quadratic RFC pairs give nonzero augmented and new recorded
steps, and a genuine nonsingular compression gives the actual raw Gram domain.
The real total step belongs to the genuine augmented observed span for every
execution. Actual prefix analyticity then lets the proved recorded-coordinate
transfer act on the already proved actual repeated augmented residual order. -/
theorem quadraticRFC_recorded_projected_order (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0)
    (hg : AnalyticAt ℝ g 0) (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g 0) k≠0 → 0<k → 0<memory k) (k : ℕ) (hk : 0<k)
    (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let method := rfcMethod memory count (E := E)
    let V := fun z => (Fin.cons (probedStep method (A z) (B z) (g z) k)
      (fun i : Fin (min (memory k) k) => probedStep method (A z) (B z) (g z) (k-1-i.val)) :
        Fin (min (memory k) k+1) → E)
    (fun z => projectedResidual (unitWindow (V z)) (probedGradient method (A z) (B z) (g z) (k+1))) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^(count+1)) := by
  -- The new normalized coordinate is the actual recorded total step, rather than its separate line or correction part.
  let method := rfcMethod memory count (E := E)
  let H := fun z => methodRun method (A z) (B z) (g z) k
  let s := fun z => probedStep method (A z) (B z) (g z)
  let d := fun z => method.direction (H z)
  let S := fun z (i : Fin (min (memory k) k)) => s z (k-1-i.val)
  let U : X → Fin (min (memory k) k+1) → E := fun z => Fin.cons (d z) (S z)
  have ht := quadraticRFC_prefix_analytic memory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun i hi => hpre i (by omega))
  have hD : AnalyticAt ℝ d 0 := (ht.2 k (Nat.lt_succ_self k)).1
  have hS (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun z => S z i) 0 := by
    have hi := i.isLt
    exact (ht.2 _ (by omega)).2.1
  have hU (i : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun z => U z i) 0 := Fin.cases hD hS i
  have hD0 : d 0=CG.direction Q (g 0) k := by
    dsimp only [d,H]
    rw [hA0,hB0]
    exact rfc_reference_direction memory count Q hQ hpos (g 0) hm k
  have hdata := rfc_reference_augmented_data memory count Q hQ hpos (g 0) hm k hpre
  have hn : ∀ i, U 0 i≠0 := by
    simpa only [U,S,s,method,hD0,hA0,hB0] using hdata.1
  have hv0 : s 0 k≠0 := by
    dsimp only [s]
    rw [hA0,hB0,(rfc_reference_pair memory count Q hQ hpos (g 0) hm k).1]
    obtain ⟨hd,hl,_⟩ := CG.invariant_line_pos Q hpos (g 0) k
      (CG.invariant Q hQ hpos (g 0) k (fun i hi => hpre i hi.le)) (hpre k le_rfl)
    exact smul_ne_zero hl.ne' hd
  have hcompression : IsUnit (correctionCompression (U 0) Q).det := by
    have hdom := (rfc_reference_coordinate_domains memory count Q hQ hpos (g 0) hm k hpre).2
    let Uref : Fin (min (memory k) k+1) → E := Fin.cons (CG.direction Q (g 0) k)
      (fun i : Fin (min (memory k) k) => probedStep method (fun _ => Q) (fun _ => Q) (g 0) (k-1-i.val))
    have he := congrArg (fun Z => (pairModel Uref Z).det) hdata.2.1
    rw [pairModel_quadratic _ Q hQ] at he
    rw [he] at hdom
    apply isUnit_iff_ne_zero.mpr
    simpa only [U,S,s,method,hD0,hA0,hB0] using hdom
  have hgram := isUnit_iff_ne_zero.mp (gram_unit_of_compression_unit (U 0) Q hcompression)
  have hspan : ∀ᶠ z in 𝓝 (0 : X), s z k∈Submodule.span ℝ (Set.range (U z)) :=
    Eventually.of_forall fun z => rfcStep_mem_augmented_coordinates memory count (A z) (B z) (g z) k
  exact regular_recorded_projection_order U (fun z => s z k)
    (fun z => probedGradient method (A z) (B z) (g z) (k+1)) (count+1)
    hU (ht.2 k (Nat.lt_succ_self k)).2.1 hn hv0 hgram hspan
      (quadraticRFC_projected_order memory count A B g hA hB hg Q hA0 hB0 hQ hpos hm k hk hpre).2

end
end krylov.Stability
