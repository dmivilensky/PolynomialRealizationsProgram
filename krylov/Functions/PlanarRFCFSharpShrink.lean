import krylov.Functions.PlanarRFCFScale
import krylov.Functions.PlanarSourceShrink

/-!
Article: main_krylov, thm:Fplanar, sharp RFC-F sources inside the true SC class.
Use: choose one actual maximizing tensor before the scale, shrink its true
scalar objective into the exact prescribed true-minimizer metric class and
retain the full original C_Y leading coefficient of its actual observed solve.
Source: attained genuine binary supremum, actual model homogeneity and the
proved true-minimizer SC shrink construction.
-/
namespace krylov.Functions
noncomputable section
open Set krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
/-- An actual RFC-F worst-case source has a true minimizer, the exact 2a
canonical tensor budget, and standard self-concordance on the complete
printed true-metric ball. Its actual observed value-model output retains
the sharp C_Y leading constant with one fourth-order loss.
Article: main_krylov, thm:Fplanar, actual true-SC sharp RFC-F realization. -/
theorem planeRFCF_sharp_true_metric_source (r a : ℝ) (hr : 0<r) (ha : 0<a) (ha₁ : a<1) :
    ∃ t : krylov.Tensor.BinaryCubic, t.InBall ∧ rfcObjective r t=rfcWorst r ∧
    ∃ ε₀ C M E : ℝ, 0<ε₀ ∧ 0<C ∧ 0<M ∧ 0<E ∧
      ∀ p : ℝ, 0<p → p<ε₀ → let α := 2*a*(1-C*p)^3
      0<α ∧ α≤2*a ∧ ∃ x : Plane,
        ‖x-planeOfPair (p,r*p)‖≤M*p^2 ∧
        ‖planeCubicHessian p r (scaleBinaryCubic α t) x-ContinuousLinearMap.id ℝ Plane‖≤C*p ∧
        PlanarTrueMetricRealization p r a α t x ∧
        |‖gradient (planeCubicObjective p r (scaleBinaryCubic α t))
            (planeRFCFOutput p r (scaleBinaryCubic α t))‖-
          a^2*r*modelMetricCoefficient r*p^3|≤E*p^4 := by
  obtain ⟨t,ht,hatt⟩ := exists_tensor_attaining_rfcWorst r
  obtain ⟨ep,C,M,hep,hC,hM,hsource⟩ := planeCubic_pair_true_metric_realization r a ha ha₁ ht ht
  obtain ⟨el,Cl,hel,hCl,hresponse⟩ := planeRFCFOutput_scaled_norm_remainder r hr.ne'
  let K := r^2/4*rfcWorst r
  have hK : 0<K := by
    have hh := (rfcWorst_bounds r).1
    dsimp only [K]
    positivity
  let E := 24*a^2*K*C+8*Cl*a^3+1
  refine ⟨t,ht,hatt,min ep (min (el/(2*a+1)) (1/(C+1))),C,M,E,by positivity,hC,hM,
    by dsimp only [E]; positivity,?_⟩
  intro p hp he
  obtain ⟨hα,hαU,x,y,hx,_,hHx,_,hxsource,_⟩ := hsource p hp (he.trans_le (min_le_left _ _))
  let q := 1-C*p
  let α := 2*a*q^3
  have hq : 0<q := by
    have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    dsimp only [q]
    nlinarith only [hh,hp]
  have hαp : α*p<el := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*a+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [mul_le_mul_of_nonneg_right hαU hp.le,hh,hp]
  refine ⟨hα,hαU,x,hx,hHx,hxsource,?_⟩
  have hb := hresponse p α hp hα hαp t ht
  rw [hatt] at hb
  have hq6 : 1-6*C*p≤q^6 := by
    have hh := one_add_mul_sub_le_pow (show -1≤q by linarith only [hq]) 6
    norm_num only [Nat.cast_ofNat] at hh
    dsimp only [q] at *
    nlinarith only [hh]
  have hα2 : 4*a^2*(1-6*C*p)≤α^2 := by
    have hh := mul_le_mul_of_nonneg_left hq6 (by positivity : 0≤4*a^2)
    dsimp only [α]
    nlinarith only [hh]
  have hα2U : α^2≤4*a^2 := (pow_le_pow_left₀ hα.le hαU 2).trans_eq (by ring)
  have hα3 : α^3≤8*a^3 := (pow_le_pow_left₀ hα.le hαU 3).trans_eq (by ring)
  have hmain := mul_le_mul_of_nonneg_right hα2 (mul_nonneg hK.le (pow_nonneg hp.le 3))
  have hupper := mul_le_mul_of_nonneg_right hα2U (mul_nonneg hK.le (pow_nonneg hp.le 3))
  have herr := mul_le_mul_of_nonneg_left hα3 (mul_nonneg hCl.le (pow_nonneg hp.le 4))
  obtain ⟨hblo,hbhi⟩ := abs_le.mp hb
  apply abs_le.mpr
  constructor <;> dsimp only [K,E,modelMetricCoefficient] at * <;>
    nlinarith only [hmain,hupper,herr,hblo,hbhi,pow_pos hp 4,mul_nonneg hK.le hC.le]

end
end krylov.Functions
