import krylov.Stability.AnalyticRFC
import krylov.LinearAlgebra.CorrectionAsymptotics

/-!
Article: Lemma B.3 [lem:projected-residual] of krylov.tex.
Use: derive first-order real total correction movements and quadratic actual
recorded-pair defects from the genuine adaptive RFC prefix, without assuming either order.
Source: the proved actual analytic RFC trajectory, true quadratic CG steps,
and exact recorded-pair/operator-mismatch identity.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference krylov.LinearAlgebra
open scoped Topology InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Actual repeated RFC total correction movements have first order and their genuine recorded secant defects have quadratic order on every nondegenerate reference prefix.
Use: fully discharge the source pair formula's O(ω²) term for real RFC/RFC_k execution, including the initial empty window.
Article: main_krylov, lem:projected-residual and apD:eq:pairs.
Proof: the real total step and exact line step are analytic, and their true
quadratic reference values coincide with the genuine CG step. Their difference
is the actual total correction, hence has first order. The true operator
mismatch also has first order; the exact actual recorded-pair identity makes
its product with the true correction the quadratic pair defect. -/
theorem quadraticRFC_pair_orders (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0)
    (hg : AnalyticAt ℝ g 0) (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hm : ∀ k, CG.gradient Q (g 0) k≠0 → 0<k → 0<memory k) (k : ℕ)
    (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let method := rfcMethod memory count (E := E)
    (fun z => (probedPhase method (A z) (B z) (g z) k).movement) =O[𝓝 (0 : X)] (fun z => ‖z‖) ∧
      (fun z => probedSecant method (A z) (B z) (g z) k-A z k (probedStep method (A z) (B z) (g z) k)) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
  -- The actual correction is recovered from actual physical steps, preserving the real executed query tree.
  let method := rfcMethod memory count (E := E)
  let H := fun z => methodRun method (A z) (B z) (g z) k
  let d := fun z => method.direction (H z)
  let z := fun p => A p k (d p)
  let line := fun p => lineLength (H p).gradient (d p) (z p) • d p
  let χ := fun p => (probedPhase method (A p) (B p) (g p) k).movement
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
  have hline : AnalyticAt ℝ line 0 := ((analytic_inner hD hG).neg.div (analytic_inner hD hZ) hcurv).smul hD
  have hχ : AnalyticAt ℝ χ 0 := by
    apply ((ht.2 k (Nat.lt_succ_self k)).2.1.sub hline).congr
    apply Eventually.of_forall
    intro p
    change (line p+χ p)-line p=χ p
    abel
  have hline0 : line 0=referenceStep Q (g 0) k := by
    dsimp only [line]
    rw [hG0,hD0,hZ0]
    rfl
  have hχ0 : χ 0=0 := by
    have hp : line 0+χ 0=referenceStep Q (g 0) k := by
      change probedStep method (A 0) (B 0) (g 0) k=referenceStep Q (g 0) k
      rw [hA0,hB0]
      exact (rfc_reference_pair memory count Q hQ hpos (g 0) hm k).1
    rw [hline0] at hp
    exact add_left_cancel (hp.trans (add_zero _).symm)
  have hχo : χ =O[𝓝 (0 : X)] (fun p => ‖p‖) := by
    simpa only [hχ0,sub_zero] using hχ.differentiableAt.isBigO_sub.norm_right
  have hBA0 : B 0 k-A 0 k=0 := by rw [hA0,hB0,sub_self]
  have hBA : (fun p => B p k-A p k) =O[𝓝 (0 : X)] (fun p => ‖p‖) := by
    have ht' := ((hB k).sub (hA k)).differentiableAt.isBigO_sub.norm_right
    change (fun p => B p k-A p k-(B 0 k-A 0 k)) =O[𝓝 (0 : X)] (fun p => ‖p-0‖) at ht'
    simpa only [hBA0,sub_zero] using ht'
  refine ⟨hχo,?_⟩
  have hp := operator_action_order (fun p => B p k-A p k) χ (fun p => ‖p‖) (fun p => ‖p‖) hBA hχo
  simpa only [probedSecant_defect_identity,pow_two] using hp

end
end krylov.Stability
