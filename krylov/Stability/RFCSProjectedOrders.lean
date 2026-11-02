import krylov.Stability.AnalyticRFCS
import krylov.Stability.RFCProjectedOrders

/-!
Article: main_krylov, thm:RFCS, actual secant-probed RFC execution.
Use: distinguish the measured probe from the real line and correction
segments throughout the genuine observed history and final residual.
Source: the actual RFC-S executor, real retained finite pair arrays and
proved positive-quadratic model/search/gate domains.
-/


namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference
open scoped Topology InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual RFC-S predicted model correction has first-order genuine coefficients and a quadratic normalized projected residual near every nondegenerate positive quadratic reference.
Use: the full final corrected prediction removes all earlier independent-probe defects at first order.
Article: main_krylov, thm:RFCS, actual predicted-model residual is O(ω²).
Proof: the actual independent-probe prefix gives genuine analytic measured
data. True quadratic execution derives nonzero augmented columns, the real
positive model and zero reference projected predicted gradient. The actual
observed gate passes locally. Apply the existing fully discharged real
model coefficient and repeated projected-residual order theorems to that
actual predicted one-query correction phase. -/
theorem quadraticRFCS_predicted_projected_order (memory : ℕ → ℕ)
    (Ap A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hAp : ∀ i, AnalyticAt ℝ (fun z => Ap z i) 0)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0)
    (hg : AnalyticAt ℝ g 0) (Q : E →L[ℝ] E) (hAp0 : Ap 0=(fun _ => Q)) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g 0) k≠0 → 0<k → 0<memory k) (k : ℕ) (hk : 0<k)
    (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let H := fun z => rfcSRun memory (Ap z) (A z) (B z) (g z) k
    let d := fun z => windowDirection (selectedWindow memory (H z)) (H z).gradient
    let U := fun z => (Fin.cons (d z) (fun i : Fin (min (memory k) k) =>
      rfcSStep memory (Ap z) (A z) (B z) (g z) (k-1-i.val)) : Fin (min (memory k) k+1) → E)
    let Z := fun z => (Fin.cons (Ap z k (d z)) (fun i : Fin (min (memory k) k) =>
      rfcSSecant memory (Ap z) (A z) (B z) (g z) (k-1-i.val)) : Fin (min (memory k) k+1) → E)
    let g' := fun z => searchedGradient (H z).gradient (d z) (Ap z k (d z))
    (fun z => modelCoefficients (U z) (pairModel (U z) (Z z)) (g' z)) =O[𝓝 (0 : X)] (fun z => ‖z‖) ∧
      (fun z => projectedResidual (unitWindow (U z)) ((rfcSPhase memory (Ap z) (A z) (B z) (g z) k).gradient)) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
  -- All reference and local-domain facts concern the actual observed trajectory and its actual finite coefficient solve.
  let H := fun z => rfcSRun memory (Ap z) (A z) (B z) (g z) k
  let s := fun z => rfcSStep memory (Ap z) (A z) (B z) (g z)
  let y := fun z => rfcSSecant memory (Ap z) (A z) (B z) (g z)
  let d := fun z => windowDirection (selectedWindow memory (H z)) (H z).gradient
  let z := fun p => Ap p k (d p)
  let S := fun p (i : Fin (min (memory k) k)) => s p (k-1-i.val)
  let Y := fun p (i : Fin (min (memory k) k)) => y p (k-1-i.val)
  let U : X → Fin (min (memory k) k+1) → E := fun p => Fin.cons (d p) (S p)
  let Z : X → Fin (min (memory k) k+1) → E := fun p => Fin.cons (z p) (Y p)
  let C := fun p => pairModel (U p) (Z p)
  let g' := fun p => searchedGradient (H p).gradient (d p) (z p)
  have ht := quadraticRFCS_prefix_analytic memory Ap A B g 0 hAp hA hB hg Q hAp0 hA0 hB0 hQ hpos hm
    (k+1) (fun i hi => hpre i (by omega))
  have hG := (quadraticRFCS_prefix_analytic memory Ap A B g 0 hAp hA hB hg Q hAp0 hA0 hB0 hQ hpos hm
    k (fun i hi => hpre i hi.le)).1
  have hD : AnalyticAt ℝ d 0 := (ht.2 k (Nat.lt_succ_self k)).1
  have hZ : AnalyticAt ℝ z 0 := analytic_operator_apply (hAp k) hD
  have hG0 : (H 0).gradient=CG.gradient Q (g 0) k := by
    dsimp only [H]
    rw [hAp0,hA0,hB0]
    exact (rfcSRun_static memory Q hQ hpos (g 0) hm k).1
  have hD0 : d 0=CG.direction Q (g 0) k := by
    dsimp only [d,H]
    rw [hAp0,hA0,hB0,rfcSRun_exact]
    exact rfc_reference_direction memory 1 Q hQ hpos (g 0) hm k
  have hZ0 : z 0=Q (CG.direction Q (g 0) k) := by dsimp only [z]; rw [hAp0,hD0]
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
  have hdata := rfc_reference_augmented_data memory 1 Q hQ hpos (g 0) hm k hpre
  have hn : ∀ i, U 0 i≠0 := by
    simpa only [U,S,s,hD0,hAp0,hA0,hB0,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.1,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.2] using hdata.1
  have hZQ : Z 0=(fun i => Q (U 0 i)) := by
    simpa only [U,Z,S,Y,s,y,hD0,hZ0,hAp0,hA0,hB0,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.1,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.2] using hdata.2.1
  have hρ0 : coordinates (U 0) (g' 0)=0 := by
    rw [hg'0]
    simpa only [U,S,s,hD0,hAp0,hA0,hB0,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.1,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.2] using hdata.2.2
  have hu : (C 0).det≠0 := by
    dsimp only [C,U,Z,S,Y,s,y]
    simp only [hD0,hZ0,hAp0,hA0,hB0,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.1,
      (rfcSFields_exact memory (fun _ => Q) (fun _ => Q) (g 0) _).2.2.2]
    exact (rfc_reference_coordinate_domains memory 1 Q hQ hpos (g 0) hm k hpre).2
  have hmodel : correctionCompression (U 0) (B 0 k)=C 0 := by
    change correctionCompression (U 0) (B 0 k)=pairModel (U 0) (Z 0)
    rw [hB0,hZQ,pairModel_quadratic _ Q hQ]
  have hshape (p : X) : (H p).pairs=executedPairs (s p) (y p) k := rfcSRun_pairs memory _ _ _ _ k
  have hgate := retained_history_gate_eventually memory H s y 0 k hshape
    (fun i hi => (ht.2 i (by omega)).2.1.continuousAt) (fun i hi => (ht.2 i (by omega)).2.2.continuousAt)
    Q hQ hpos (fun i => hn i.succ) (fun i => congrFun hZQ i.succ)
    (by have := hm k (hpre k le_rfl) hk; omega)
  refine ⟨regular_model_coefficients_order U C g' hU hC hg' hu hρ0,?_⟩
  have hres := regular_repeated_model_projected_order U C (fun p => B p k) g' 1 hU hC (hB k) hg' hn hu hmodel hρ0
  apply hres.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hgate] with p hp
  have hq := rfcCorrection_coordinates memory 1 (H p) (s p) (y p) k (d p) (z p) (hshape p) rfl hp
  change projectedResidual (unitWindow (U p)) (runCorrections (repeatedModelTree (U p) (C p) 1 (g' p)) (B p k) (g' p)).gradient=
    projectedResidual (unitWindow (U p)) (runCorrections (rfcCorrection memory 1 (H p) (z p)) (B p k) (g' p)).gradient
  rw [hq]

end
end krylov.Stability
