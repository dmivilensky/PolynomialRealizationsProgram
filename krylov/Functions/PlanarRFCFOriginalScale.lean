import krylov.Functions.PlanarRFCFBetaScale

/-!
Article: main_krylov, thm:Fplanar, the original full tensor-budget supremum.
Use: keep the genuine scalar observed solve, independent original beta and
arbitrary positive tensor amplitude in the same finite-scale theorem.
Source: exact independent-base model homogeneity and the proved true uniform
response. In particular alpha=2(1-delta) has its printed squared amplitude.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000 in
/-- The actual original-base observed solve has its exact squared tensor
amplitude, uniformly over every independent original |beta|≤B*p.
Article: main_krylov, thm:Fplanar, complete tensor-budget response. -/
theorem planeUnknownBaseRFCFOutput_scaled_norm_remainder (r B α : ℝ)
    (hr : r≠0) (hB : 0≤B) (hα : 0<α) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p β : ℝ, 0<p → p<ep → |β|≤B*p →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      |‖gradient (planeUnknownBaseObjective p r β (scaleBinaryCubic α t))
          (planeUnknownBaseRFCFOutput p r β (scaleBinaryCubic α t))‖-
        α^2*(r^2/4*rfcObjective r t)*p^3|≤C*p^4 := by
  obtain ⟨el,Cl,hel,hCl,hrem⟩ := planeUnknownBaseRFCFOutput_norm_remainder r (B/α) hr (div_nonneg hB hα.le)
  let L := B+α*(1+|r|)/2
  have hL : 0≤L := by dsimp only [L]; positivity
  refine ⟨min (el/α) (1/(2*(L+1))),Cl*α^3,by positivity,by positivity,?_⟩
  intro p β hp he hβ t ht
  have ht2 : |t.t2|≤1 := by
    have hh := (coefficient_disks ht).2
    rw [abs_le]
    constructor <;> nlinarith only [hh,sq_nonneg t.t1]
  have ht3 := (axis_bounds ht).2
  have hsum : |t.t2+r*t.t3|≤1+|r| := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    nlinarith only [ht2,mul_le_mul_of_nonneg_left ht3 (abs_nonneg r)]
  have hshift : |β+(α*p)*(t.t2+r*t.t3)/2|≤L*p := by
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_mul,abs_of_pos (mul_pos hα hp),show |(2:ℝ)|=2 by norm_num]
    have hh := mul_le_mul_of_nonneg_left hsum (mul_nonneg hα.le hp.le)
    dsimp only [L]
    nlinarith only [hβ,hh]
  have hpL : L*p≤1/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(L+1))).mp (he.trans_le (min_le_right _ _))
    nlinarith only [hh,hp]
  have hβdomain : 1+(β+(α*p)*(t.t2+r*t.t3)/2)≠0 := by
    have hh := (abs_le.mp (hshift.trans hpL)).1
    linarith
  have hsmall : α*p<el := by
    have hh := (lt_div_iff₀ hα).mp (he.trans_le (min_le_left _ _))
    nlinarith only [hh]
  have hβscaled : |β|≤(B/α)*(α*p) := hβ.trans_eq (by field_simp)
  have hb := hrem (α*p) β (mul_pos hα hp) hsmall hβscaled t ht
  have heq : ‖gradient (planeUnknownBaseObjective p r β (scaleBinaryCubic α t))
        (planeUnknownBaseRFCFOutput p r β (scaleBinaryCubic α t))‖-
      α^2*(r^2/4*rfcObjective r t)*p^3=
      α⁻¹*(‖gradient (planeUnknownBaseObjective (α*p) r β t)
        (planeUnknownBaseRFCFOutput (α*p) r β t)‖-(r^2/4*rfcObjective r t)*(α*p)^3) := by
    rw [planeUnknownBaseRFCFOutput_gradient_tensor_scale p r β α hp.ne' hr hα t hβdomain]
    field_simp
  rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hα)]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hα.le)).trans_eq (by field_simp)

/-- The actual original independent-base RFC-F worst case at the full
positive tensor-budget amplitude. Article: main_krylov, thm:Fplanar. -/
def planeUnknownBaseScaledRFCFActualWorst (p r B α : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (β : ℝ) (t : krylov.Tensor.BinaryCubic), |β|≤B*p ∧ t.InBall ∧
    v=‖gradient (planeUnknownBaseObjective p r β (scaleBinaryCubic α t))
      (planeUnknownBaseRFCFOutput p r β (scaleBinaryCubic α t))‖}

set_option maxHeartbeats 1000000 in
/-- The full original independent-base, full tensor-budget supremum equals
the printed C_Y coefficient up to one uniform fourth-order error. Taking
alpha=2(1-delta) yields precisely (1-delta)^2*r*C_Y(r)*p³.
Article: main_krylov, thm:Fplanar, complete original planar supremum. -/
theorem planeUnknownBaseScaledRFCFActualWorst_remainder (r B α : ℝ)
    (hr : 0<r) (hB : 0≤B) (hα : 0<α) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ep →
      |planeUnknownBaseScaledRFCFActualWorst p r B α-
        (α^2*r/4*modelMetricCoefficient r)*p^3|≤C*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeUnknownBaseRFCFOutput_scaled_norm_remainder r B α hr.ne' hB hα
  obtain ⟨tstar,htstar,hstar⟩ := exists_tensor_attaining_rfcWorst r
  refine ⟨ep,C,hep,hC,?_⟩
  intro p hp he
  let K := (α^2*r/4*modelMetricCoefficient r)*p^3
  let F := fun β t=>‖gradient (planeUnknownBaseObjective p r β (scaleBinaryCubic α t))
    (planeUnknownBaseRFCFOutput p r β (scaleBinaryCubic α t))‖
  let V := {v : ℝ | ∃ (β : ℝ) (t : krylov.Tensor.BinaryCubic), |β|≤B*p ∧ t.InBall ∧ v=F β t}
  have hzero : |(0:ℝ)|≤B*p := by rw [abs_zero]; positivity
  have hne : V.Nonempty := ⟨_,0,tstar,hzero,htstar,rfl⟩
  have hcoeff : α^2*(r^2/4*rfcWorst r)*p^3=K := by dsimp only [K,modelMetricCoefficient]; ring
  have hnorm β (hβ : |β|≤B*p) t (ht : t.InBall) : |F β t-α^2*(r^2/4*rfcObjective r t)*p^3|≤C*p^4 :=
    hrem p β hp he hβ t ht
  have hupper v (hv : v∈V) : v≤K+C*p^4 := by
    obtain ⟨β,t,hβ,ht,rfl⟩ := hv
    have hh := (abs_le.mp (hnorm β hβ t ht)).2
    have hb := le_csSup (rfcValues_bddAbove r) (show rfcObjective r t∈rfcValues r from ⟨t,ht,rfl⟩)
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hb (by positivity : 0≤r^2/4)) (sq_nonneg α)) (pow_nonneg hp.le 3)
    change α^2*(r^2/4*rfcObjective r t)*p^3≤α^2*(r^2/4*rfcWorst r)*p^3 at hm
    rw [hcoeff] at hm
    linarith only [hh,hm]
  have hbounded : BddAbove V := ⟨K+C*p^4,hupper⟩
  have hWupper : planeUnknownBaseScaledRFCFActualWorst p r B α≤K+C*p^4 := csSup_le hne hupper
  have hWlower : K-C*p^4≤planeUnknownBaseScaledRFCFActualWorst p r B α := by
    have hh := (abs_le.mp (hnorm 0 hzero tstar htstar)).1
    rw [hstar,hcoeff] at hh
    have hm : F 0 tstar≤planeUnknownBaseScaledRFCFActualWorst p r B α := le_csSup hbounded ⟨0,tstar,hzero,htstar,rfl⟩
    linarith only [hh,hm]
  change |planeUnknownBaseScaledRFCFActualWorst p r B α-K|≤C*p^4
  exact abs_le.mpr ⟨by linarith only [hWlower],by linarith only [hWupper]⟩

end
end krylov.Functions
