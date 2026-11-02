import krylov.Stability.RFCRecordedOrders
import krylov.Stability.CanonicalProjectionOrder

/-!
Article: main_krylov, lem:projected-residual, actual canonical RFC prefix orders.
Use: state both true augmented and true recorded-window orders in the genuine
positive-root canonical metric used by the article.
Source: the proved actual RFC prefix orders, real CG reference data and exact
primal/dual canonical projection-order transfer.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference krylov.Secant
open scoped Topology InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n : ℕ}

/-- Actual repeated RFC augmented and newly recorded projected residuals have order c+1 in the source's genuine canonical metric.
Use: both canonical prefix orders concern real executed gradients and actual positive-root normalized physical columns.
Article: main_krylov, lem:projected-residual, complete noninitial canonical RFC_k orders.
Proof: the genuine analytic prefix gives true nonzero augmented and recorded
reference columns. Apply both proved real physical RFC order theorems and then
the exact actual canonical projection transfer, whose only coordinate factors
are proved locally bounded ratios of genuine physical and canonical step norms. -/
theorem quadraticRFC_canonical_projection_orders (memory : ℕ → ℕ) (count : ℕ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : X → EuclideanSpace ℝ (Fin n))
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0)
    (hg : AnalyticAt ℝ g 0) (hA0 : A 0=(fun _ => cgOperator base)) (hB0 : B 0=(fun _ => cgOperator base))
    (hm : ∀ k, CG.gradient (cgOperator base) (g 0) k≠0 → 0<k → 0<memory k) (k : ℕ) (hk : 0<k)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) (g 0) i≠0) :
    let method := rfcMethod memory count (E := EuclideanSpace ℝ (Fin n))
    let H := fun z => methodRun method (A z) (B z) (g z) k
    let d := fun z => method.direction (H z)
    let S := fun z (i : Fin (min (memory k) k)) => probedStep method (A z) (B z) (g z) (k-1-i.val)
    let U : X → Fin (min (memory k) k+1) → EuclideanSpace ℝ (Fin n) := fun z => Fin.cons (d z) (S z)
    let V : X → Fin (min (memory k) k+1) → EuclideanSpace ℝ (Fin n) :=
      fun z => Fin.cons (probedStep method (A z) (B z) (g z) k) (S z)
    let gplus := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (probedGradient method (A z) (B z) (g z) (k+1))
    (fun z => projectedResidual (unitWindow (primalWindow base (U z))) (gplus z)) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^(count+1)) ∧
      (fun z => projectedResidual (unitWindow (primalWindow base (V z))) (gplus z)) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^(count+1)) := by
  -- Canonical normalizers are built from the actual metric root and actual physical executed columns.
  let Q := cgOperator base
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  let method := rfcMethod memory count (E := EuclideanSpace ℝ (Fin n))
  let H := fun z => methodRun method (A z) (B z) (g z) k
  let s := fun z => probedStep method (A z) (B z) (g z)
  let d := fun z => method.direction (H z)
  let S := fun z (i : Fin (min (memory k) k)) => s z (k-1-i.val)
  let U : X → Fin (min (memory k) k+1) → EuclideanSpace ℝ (Fin n) := fun z => Fin.cons (d z) (S z)
  let V : X → Fin (min (memory k) k+1) → EuclideanSpace ℝ (Fin n) := fun z => Fin.cons (s z k) (S z)
  have ht := quadraticRFC_prefix_analytic memory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun i hi => hpre i (by omega))
  have hS (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun z => S z i) 0 := by
    have hi := i.isLt
    exact (ht.2 _ (by omega)).2.1
  have hU (i : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun z => U z i) 0 :=
    Fin.cases (ht.2 k (Nat.lt_succ_self k)).1 hS i
  have hV (i : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun z => V z i) 0 :=
    Fin.cases (ht.2 k (Nat.lt_succ_self k)).2.1 hS i
  have hD0 : d 0=CG.direction Q (g 0) k := by
    dsimp only [d,H]
    rw [hA0,hB0]
    exact rfc_reference_direction memory count Q hQ hpos (g 0) hm k
  have hdata := rfc_reference_augmented_data memory count Q hQ hpos (g 0) hm k hpre
  have hnU : ∀ i, U 0 i≠0 := by
    simpa only [U,S,s,method,hD0,hA0,hB0] using hdata.1
  have hnV : ∀ i, V 0 i≠0 := by
    intro i
    refine Fin.cases ?_ (fun j => hnU j.succ) i
    change s 0 k≠0
    dsimp only [s]
    rw [hA0,hB0,(rfc_reference_pair memory count Q hQ hpos (g 0) hm k).1]
    obtain ⟨hd,hl,_⟩ := CG.invariant_line_pos Q hpos (g 0) k
      (CG.invariant Q hQ hpos (g 0) k (fun i hi => hpre i hi.le)) (hpre k le_rfl)
    exact smul_ne_zero hl.ne' hd
  constructor
  · exact canonical_projectedResidual_order base hb U _ (count+1) (fun i => (hU i).continuousAt) hnU
      (quadraticRFC_projected_order memory count A B g hA hB hg Q hA0 hB0 hQ hpos hm k hk hpre).2
  · exact canonical_projectedResidual_order base hb V _ (count+1) (fun i => (hV i).continuousAt) hnV
      (quadraticRFC_recorded_projected_order memory count A B g hA hB hg Q hA0 hB0 hQ hpos hm k hk hpre)

end
end krylov.Stability
