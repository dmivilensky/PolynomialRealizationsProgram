import krylov.Correction.RFCSLastProbe
import krylov.Correction.CanonicalExpansion

/-!
Article: main_krylov, thm:RFCS, genuine only-last-probe first-order expansion.
Use: the actual independently probed RFC-S executor has only its final
probe mismatch in the true first variation, with a derived quadratic remainder.
Source: actual analytic measured histories, the genuine predicted-model
projected residual, full reference rank and exact physical mismatch balance.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant krylov.Variation
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {k : ℕ}

/-- The actual RFC-S measured probe operator with its original independent canonical probe-to-line mismatch.
Use: genuine line and evaluated correction segments remain the original physical canonical source operators.
Article: main_krylov, thm:RFCS, Aᵖ_k=A_k−A¹ᐟ²Eᵖ_kA¹ᐟ². -/
def rfcsCanonicalProbe (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (E P : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (i : ℕ) :
    EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  canonicalFCPath base E 1 i-cgOperator (metricRoot base*P i*metricRoot base)

/-- The actual independent-probe RFC-S terminal gradient has exactly the last original canonical probe mismatch times the true terminal CG unit step, with a genuine quadratic remainder.
Use: this is the printed source operator expansion for the real evaluated run, derived entirely from primitive canonical increment and probe-defect regularity.
Article: main_krylov, thm:RFCS, A^(−1/2)g_n=‖e_last‖_A Eᵖ_last ŝ_last+O(ω²).
Proof: original canonical increments and independently prescribed probe
mismatches give actual analytic line and probe operators with the true
quadratic reference. Apply the genuine physical last-probe theorem. The
actual inverse metric root cancels its left source congruence exactly;
the true reference step normalizes to its original unit CG direction. -/
theorem full_rfcs_canonical_first_order
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (E P : X → ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hE : ∀ i, AnalyticAt ℝ (fun x => E x i) 0) (hP : ∀ i, AnalyticAt ℝ (fun x => P x i) 0)
    (hE0 : ∀ i, E 0 i=0) (hP0 : ∀ i, P 0 i=0) :
    (fun x => cgOperator (metricRoot base)⁻¹ (rfcSGradient fullMemory (rfcsCanonicalProbe base (E x) (P x))
        (canonicalFCPath base (E x) 1) (canonicalFCPath base (E x) 1) g (k+1))-
      ‖canonicalCGStep base g k‖ • cgOperator (P x k) (canonicalCGUnitStep base g k))
      =O[𝓝 (0 : X)] (fun x => ‖x‖^2) := by
  -- Primitive original source coordinates derive all genuine independent-probe operator regularity.
  let A := fun x => canonicalFCPath base (E x) 1
  let Ap := fun x => rfcsCanonicalProbe base (E x) (P x)
  have hA (i : ℕ) : AnalyticAt ℝ (fun x => A x i) 0 :=
    canonicalFCPath_analyticAt (fun _ => base) E 0 analyticAt_const (Filter.Eventually.of_forall fun _ => hb) hE i
  have hAp (i : ℕ) : AnalyticAt ℝ (fun x => Ap x i) 0 := by
    have hm : AnalyticAt ℝ (fun x => metricRoot base*P x i*metricRoot base) 0 :=
      (analyticAt_const.mul (hP i)).mul analyticAt_const
    exact (hA i).sub ((matrixOperator_contDiffAt _ 0 hm.contDiffAt).analyticAt)
  have hA0 : A 0=(fun _ => cgOperator base) := canonicalFCPath_at_zero base (E 0) hE0
  have hAp0 : Ap 0=(fun _ => cgOperator base) := by
    funext i
    simp only [Ap,rfcsCanonicalProbe,hP0,Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero,sub_zero]
    exact congrFun hA0 i
  -- Normalize the actual physical output expansion and cancel only the true fixed metric roots.
  have hphysical := full_rfcs_last_probe_order base hb g hN hk Ap A A hAp hA hA hAp0 hA0 hA0
  have hnormalized := operator_action_order (fun _ : X => cgOperator (metricRoot base)⁻¹) _
    (fun _ => 1) (fun x => ‖x‖^2) (continuousAt_const.tendsto.isBigO_one ℝ) hphysical
  have hnormalized' : (fun x => cgOperator (metricRoot base)⁻¹
      (rfcSGradient fullMemory (Ap x) (A x) (A x) g (k+1)-(A x k-Ap x k) (referenceStep (cgOperator base) g k)))
      =O[𝓝 (0 : X)] (fun x => ‖x‖^2) := by simpa only [one_mul] using hnormalized
  apply hnormalized'.congr_left
  intro x
  rw [map_sub]
  have hmismatch : A x k-Ap x k=cgOperator (metricRoot base*P x k*metricRoot base) := by
    dsimp only [A,Ap,rfcsCanonicalProbe]
    abel
  rw [hmismatch]
  have hcancel (u : EuclideanSpace ℝ (Fin (k+1))) :
      cgOperator (metricRoot base)⁻¹ (cgOperator (metricRoot base*P x k*metricRoot base) u)=
        cgOperator (P x k) (cgOperator (metricRoot base) u) := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,← Matrix.mul_assoc,
      nonsing_inv_mul _ (metricRoot_det_unit base hb),Matrix.one_mul]
  rw [hcancel]
  change _-cgOperator (P x k) (canonicalCGStep base g k)=_
  have hstep : canonicalCGStep base g k=‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k :=
    (NormedSpace.norm_smul_normalize _).symm
  have ha : cgOperator (P x k) (canonicalCGStep base g k)=
      ‖canonicalCGStep base g k‖ • cgOperator (P x k) (canonicalCGUnitStep base g k) := by
    calc
      _ = cgOperator (P x k) (‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k) := congrArg (cgOperator (P x k)) hstep
      _ = _ := map_smul _ _ _
  rw [ha]

end
end krylov.Correction
