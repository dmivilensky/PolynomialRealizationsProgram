import krylov.Functions.PlanarRFCFBetaResponse
import krylov.Functions.PlanarRFCFWorst

/-!
Article: main_krylov, thm:Fplanar, all independent unknown planar bases.
Use: take the actual observed-solve supremum jointly over the full tensor
ball and the independent interval |beta|≤B*p. Source: the proved genuine
scalar-model response, true tensor maximizer and conditional supremum rules.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The actual value-model RFC-F worst case over the entire independent
unknown-base interval and original binary tensor ball. Article: thm:Fplanar. -/
def planeBetaRFCFActualWorst (p r B : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (β : ℝ) (t : krylov.Tensor.BinaryCubic), |β|≤B*p ∧ t.InBall ∧
    v=‖gradient (planeBetaCubicObjective p r β t) (planeBetaRFCFOutput p r β t)‖}

/-- The pointwise true observed-solve response is uniform in the original
independent beta interval, with no division-based normalization premise.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaRFCFOutput_interval_remainder (r B : ℝ) (hr : r≠0) (hB : 0≤B) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p β : ℝ, 0<p → p<ep → |β|≤B*p →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      |‖gradient (planeBetaCubicObjective p r β t) (planeBetaRFCFOutput p r β t)‖-
        (r^2/4*rfcObjective r t)*p^3|≤C*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeBetaRFCFOutput_norm_remainder r B hr hB
  refine ⟨ep,C,hep,hC,?_⟩
  intro p β hp he hβ t ht
  have hb : |β/p|≤B := by
    rw [abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr hβ
  have hh := hrem p (β/p) hp he hb t ht
  simpa only [mul_div_cancel₀ β hp.ne'] using hh

set_option maxHeartbeats 1000000 in
/-- Taking the full tensor supremum and the independent unknown-base
supremum leaves exactly the printed C_Y coefficient, with a proved uniform
fourth-order error. Every output uses the actual reconstructed scalar model.
Article: main_krylov, thm:Fplanar, independent-beta C_Y equality. -/
theorem planeBetaRFCFActualWorst_remainder (r B : ℝ) (hr : 0<r) (hB : 0≤B) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ep →
      |planeBetaRFCFActualWorst p r B-(r/4*modelMetricCoefficient r)*p^3|≤C*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeBetaRFCFOutput_interval_remainder r B hr.ne' hB
  obtain ⟨tstar,htstar,hstar⟩ := exists_tensor_attaining_rfcWorst r
  refine ⟨ep,C,hep,hC,?_⟩
  intro p hp he
  let K := (r/4*modelMetricCoefficient r)*p^3
  let F := fun β t=>‖gradient (planeBetaCubicObjective p r β t) (planeBetaRFCFOutput p r β t)‖
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
  have hWupper : planeBetaRFCFActualWorst p r B≤K+C*p^4 := csSup_le hne hupper
  have hWlower : K-C*p^4≤planeBetaRFCFActualWorst p r B := by
    have hh := (abs_le.mp (hnorm 0 hzero tstar htstar)).1
    rw [hstar,hcoeff] at hh
    have hm : F 0 tstar≤planeBetaRFCFActualWorst p r B := le_csSup hbounded ⟨0,tstar,hzero,htstar,rfl⟩
    linarith only [hh,hm]
  change |planeBetaRFCFActualWorst p r B-K|≤C*p^4
  exact abs_le.mpr ⟨by linarith only [hWlower],by linarith only [hWupper]⟩

end
end krylov.Functions
