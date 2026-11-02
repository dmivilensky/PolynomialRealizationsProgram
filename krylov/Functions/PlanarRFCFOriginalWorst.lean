import krylov.Functions.PlanarRFCFUnknownBase

/-!
Article: main_krylov, thm:Fplanar, the original independent-base supremum.
Use: state the full C_Y equality with the source's actual A0=I+beta*h*hᵀ,
optimizing over every independent beta and genuine binary tensor. Source:
true first-midpoint Hessian dictionary, genuine scalar observed-model solve,
uniform fourth-order response and an actual binary-objective maximizer.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The genuine actual observed-model worst case, with the ORIGINAL unknown
base independent of the true cubic. Article: main_krylov, thm:Fplanar. -/
def planeUnknownBaseRFCFActualWorst (p r B : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (β : ℝ) (t : krylov.Tensor.BinaryCubic), |β|≤B*p ∧ t.InBall ∧
    v=‖gradient (planeUnknownBaseObjective p r β t) (planeUnknownBaseRFCFOutput p r β t)‖}

set_option maxHeartbeats 1000000 in
/-- The complete original planar unknown-base RFC-F supremum has exactly
C_Y as its leading coefficient. Both suprema are over the actual original
independent uncertainty parameters, and every returned point is the genuine
scalar observed-model solve. Article: main_krylov, thm:Fplanar. -/
theorem planeUnknownBaseRFCFActualWorst_remainder (r B : ℝ) (hr : 0<r) (hB : 0≤B) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ep →
      |planeUnknownBaseRFCFActualWorst p r B-(r/4*modelMetricCoefficient r)*p^3|≤C*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeUnknownBaseRFCFOutput_norm_remainder r B hr.ne' hB
  obtain ⟨tstar,htstar,hstar⟩ := exists_tensor_attaining_rfcWorst r
  refine ⟨ep,C,hep,hC,?_⟩
  intro p hp he
  let K := (r/4*modelMetricCoefficient r)*p^3
  let F := fun β t=>‖gradient (planeUnknownBaseObjective p r β t) (planeUnknownBaseRFCFOutput p r β t)‖
  let V := {v : ℝ | ∃ (β : ℝ) (t : krylov.Tensor.BinaryCubic), |β|≤B*p ∧ t.InBall ∧ v=F β t}
  have hzero : |(0:ℝ)|≤B*p := by rw [abs_zero]; positivity
  have hne : V.Nonempty := ⟨_,0,tstar,hzero,htstar,rfl⟩
  have hcoeff : r^2/4*rfcWorst r*p^3=K := by dsimp only [K,modelMetricCoefficient]; ring
  have hnorm β (hβ : |β|≤B*p) t (ht : t.InBall) : |F β t-r^2/4*rfcObjective r t*p^3|≤C*p^4 :=
    hrem p β hp he hβ t ht
  have hupper v (hv : v∈V) : v≤K+C*p^4 := by
    obtain ⟨β,t,hβ,ht,rfl⟩ := hv
    have hh := (abs_le.mp (hnorm β hβ t ht)).2
    have hb := le_csSup (rfcValues_bddAbove r) (show rfcObjective r t∈rfcValues r from ⟨t,ht,rfl⟩)
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity : 0≤r^2/4)) (pow_nonneg hp.le 3)
    change r^2/4*rfcObjective r t*p^3≤r^2/4*rfcWorst r*p^3 at hm
    rw [hcoeff] at hm
    linarith only [hh,hm]
  have hbounded : BddAbove V := ⟨K+C*p^4,hupper⟩
  have hWupper : planeUnknownBaseRFCFActualWorst p r B≤K+C*p^4 := csSup_le hne hupper
  have hWlower : K-C*p^4≤planeUnknownBaseRFCFActualWorst p r B := by
    have hh := (abs_le.mp (hnorm 0 hzero tstar htstar)).1
    rw [hstar,hcoeff] at hh
    have hm : F 0 tstar≤planeUnknownBaseRFCFActualWorst p r B := le_csSup hbounded ⟨0,tstar,hzero,htstar,rfl⟩
    linarith only [hh,hm]
  change |planeUnknownBaseRFCFActualWorst p r B-K|≤C*p^4
  exact abs_le.mpr ⟨by linarith only [hWlower],by linarith only [hWupper]⟩

end
end krylov.Functions
