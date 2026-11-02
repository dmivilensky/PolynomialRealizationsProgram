import krylov.Stability.AnalyticRFC
import krylov.Stability.RegularModelOrders
import krylov.Methods.RFCCoordinates

/-!
Article: main_krylov, lem:projected-residual, actual RFC prefix residual orders.
Use: apply the normalized repeated-residual theorem to the actual adaptive RFC
trajectory, deriving every regularity, reference projection and inverse premise.
Source: the proved genuine RFC analytic induction, actual quadratic CG arrays,
strict real observed gates and exact finite physical decision-tree coordinates.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference
open scoped Topology InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual repeated RFC gradient after every noninitial nondegenerate reference step has its normalized augmented projected-residual order c+1.
Use: all incoming-order, real inverse-domain and actual-prefix regularity premises of the generic estimate are discharged.
Article: main_krylov, lem:projected-residual, actual RFC_k prefix O(ω^(c+1)).
Proof: genuine RFC prefix analyticity supplies the actual retained steps and
secants. True CG reference arrays give nonzero augmented columns, the real
positive model determinant and zero projected post-search gradient. The actual
observed gate passes on a proved neighborhood; its real correction tree is the
fixed-coordinate model tree, so the fully discharged normalized order theorem
applies to the actual returned gradient. -/
theorem quadraticRFC_projected_order (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0)
    (hg : AnalyticAt ℝ g 0) (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g 0) k≠0 → 0<k → 0<memory k) (k : ℕ) (hk : 0<k)
    (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let method := rfcMethod memory count (E := E)
    let H := fun z => methodRun method (A z) (B z) (g z) k
    let d := fun z => windowDirection (selectedWindow memory (H z)) (H z).gradient
    let U := fun z => (Fin.cons (d z) (fun i : Fin (min (memory k) k) =>
      probedStep method (A z) (B z) (g z) (k-1-i.val)) : Fin (min (memory k) k+1) → E)
    let Z := fun z => (Fin.cons (A z k (d z)) (fun i : Fin (min (memory k) k) =>
      probedSecant method (A z) (B z) (g z) (k-1-i.val)) : Fin (min (memory k) k+1) → E)
    let g' := fun z => searchedGradient (H z).gradient (d z) (A z k (d z))
    (fun z => modelCoefficients (U z) (pairModel (U z) (Z z)) (g' z)) =O[𝓝 (0 : X)] (fun z => ‖z‖) ∧
      (fun z => projectedResidual (unitWindow (U z)) (probedGradient method (A z) (B z) (g z) (k+1))) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^(count+1)) := by
  -- All reference and local-domain facts concern the actual observed trajectory and its actual finite coefficient solve.
  let method := rfcMethod memory count (E := E)
  let H := fun z => methodRun method (A z) (B z) (g z) k
  let s := fun z => probedStep method (A z) (B z) (g z)
  let y := fun z => probedSecant method (A z) (B z) (g z)
  let d := fun z => windowDirection (selectedWindow memory (H z)) (H z).gradient
  let z := fun p => A p k (d p)
  let S := fun p (i : Fin (min (memory k) k)) => s p (k-1-i.val)
  let Y := fun p (i : Fin (min (memory k) k)) => y p (k-1-i.val)
  let U : X → Fin (min (memory k) k+1) → E := fun p => Fin.cons (d p) (S p)
  let Z : X → Fin (min (memory k) k+1) → E := fun p => Fin.cons (z p) (Y p)
  let C := fun p => pairModel (U p) (Z p)
  let g' := fun p => searchedGradient (H p).gradient (d p) (z p)
  have ht := quadraticRFC_prefix_analytic memory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    (k+1) (fun i hi => hpre i (by omega))
  have hG := (quadraticRFC_prefix_analytic memory count A B g 0 hA hB hg Q hA0 hB0 hQ hpos hm
    k (fun i hi => hpre i hi.le)).1
  have hD : AnalyticAt ℝ d 0 := (ht.2 k (Nat.lt_succ_self k)).1
  have hZ : AnalyticAt ℝ z 0 := analytic_operator_apply (hA k) hD
  have hG0 : (H 0).gradient=CG.gradient Q (g 0) k := by
    dsimp only [H]
    rw [hA0,hB0]
    exact (rfcMethod_static memory count Q hQ hpos (g 0) hm k).1
  have hD0 : d 0=CG.direction Q (g 0) k := by
    dsimp only [d,H]
    rw [hA0,hB0]
    exact rfc_reference_direction memory count Q hQ hpos (g 0) hm k
  have hZ0 : z 0=Q (CG.direction Q (g 0) k) := by dsimp only [z]; rw [hA0,hD0]
  have hcurv : inner ℝ (d 0) (z 0)≠0 := by
    rw [hD0,hZ0]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g 0) k
      (CG.invariant Q hQ hpos (g 0) k (fun i hi => hpre i hi.le)) (hpre k le_rfl)).1).ne'
  have hα := (analytic_inner hD hG).neg.div (analytic_inner hD hZ) hcurv
  have hg' : AnalyticAt ℝ g' 0 := hG.add (hα.smul hZ)
  have hg'0 : g' 0=CG.gradient Q (g 0) (k+1) := by
    dsimp only [g']
    rw [hG0,hD0,hZ0]
    rfl
  have hS (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun p => S p i) 0 := by
    have hi := i.isLt
    exact (ht.2 _ (by omega)).2.1
  have hY (i : Fin (min (memory k) k)) : AnalyticAt ℝ (fun p => Y p i) 0 := by
    have hi := i.isLt
    exact (ht.2 _ (by omega)).2.2
  have hU (i : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun p => U p i) 0 := Fin.cases hD hS i
  have hZi (i : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun p => Z p i) 0 := Fin.cases hZ hY i
  have hC (i j : Fin (min (memory k) k+1)) : AnalyticAt ℝ (fun p => C p i j) 0 :=
    analytic_inner (hU _) (hZi _)
  have hdata := rfc_reference_augmented_data memory count Q hQ hpos (g 0) hm k hpre
  have hn : ∀ i, U 0 i≠0 := by
    simpa only [U,S,s,method,hD0,hA0,hB0] using hdata.1
  have hZQ : Z 0=(fun i => Q (U 0 i)) := by
    simpa only [U,Z,S,Y,s,y,method,hD0,hZ0,hA0,hB0] using hdata.2.1
  have hρ0 : coordinates (U 0) (g' 0)=0 := by
    rw [hg'0]
    simpa only [U,S,s,method,hD0,hA0,hB0] using hdata.2.2
  have hu : (C 0).det≠0 := by
    dsimp only [C,U,Z,S,Y,s,y]
    rw [hD0,hZ0,hA0,hB0]
    exact (rfc_reference_coordinate_domains memory count Q hQ hpos (g 0) hm k hpre).2
  have hmodel : correctionCompression (U 0) (B 0 k)=C 0 := by
    change correctionCompression (U 0) (B 0 k)=pairModel (U 0) (Z 0)
    rw [hB0,hZQ,pairModel_quadratic _ Q hQ]
  have hshape (p : X) : (H p).pairs=executedPairs (s p) (y p) k := methodRun_pairs_executed method _ _ _ k
  have hgate := retained_history_gate_eventually memory H s y 0 k hshape
    (fun i hi => (ht.2 i (by omega)).2.1.continuousAt) (fun i hi => (ht.2 i (by omega)).2.2.continuousAt)
    Q hQ hpos (fun i => hn i.succ) (fun i => congrFun hZQ i.succ)
    (by have := hm k (hpre k le_rfl) hk; omega)
  refine ⟨regular_model_coefficients_order U C g' hU hC hg' hu hρ0,?_⟩
  have hres := regular_repeated_model_projected_order U C (fun p => B p k) g' count hU hC (hB k) hg' hn hu hmodel hρ0
  apply hres.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hgate] with p hp
  have hq := rfcCorrection_coordinates memory count (H p) (s p) (y p) k (d p) (z p) (hshape p) rfl hp
  change projectedResidual (unitWindow (U p)) (runCorrections (repeatedModelTree (U p) (C p) count (g' p)) (B p k) (g' p)).gradient=
    projectedResidual (unitWindow (U p)) (runCorrections (rfcCorrection memory count (H p) (z p)) (B p k) (g' p)).gradient
  rw [hq]

end
end krylov.Stability
