import jacobi.Elliptic.Ratio
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Theorem D.5.
Endpoint constants are evaluated by actual primitives. Together with the
strict derivative sign this identifies the entire range of the calibration
ratio; this assertion does not yet identify the variational infimum.
Source: dominated convergence, the fundamental theorem of calculus and the intermediate value theorem.
Use: specializes to both i_2 and kappa, including the singular parameter endpoints.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Dominated continuity of the weighted quadrature for a bounded continuous numerator.
Use: specializes to both i_2 and kappa, including the singular parameter endpoints.
Article: jacobi, Theorem D.5.
Proof: use the parameter-independent endpoint majorant and positivity of P inside (0,1). -/
theorem weighted_quadrature_continuous (A : ℝ → ℝ → ℝ)
    (hm : ∀ t, Measurable (A t))
    (hc : ∀ v ∈ Ioo (0 : ℝ) 1, ContinuousOn (fun t => A t v) (Icc 0 1))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, |A t v| ≤ 1) :
    ContinuousOn (fun t => ∫ v in (0 : ℝ)..1, A t v*quadratureWeight t 0 v) (Icc 0 1) := by
  -- Work with the equal open-interval integral to remove the two harmless endpoint representatives.
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp endpointWeight_integrable
  have H := MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (s := Icc (0 : ℝ) 1)
    (F := fun t v => A t v*quadratureWeight t 0 v) (bound := endpointWeight)
    (fun t _ => by
      have hw : Measurable (quadratureWeight t 0) := by unfold quadratureWeight P r q; fun_prop
      exact ((hm t).mul hw).aestronglyMeasurable)
    (fun t ht => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      have hw := quadratureWeight_bound ht (by norm_num : (0 : ℝ) ∈ Icc 0 1) hv
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw.1]
      exact (mul_le_mul_of_nonneg_right (hb t ht v hv) hw.1).trans
        (by simpa only [one_mul] using hw.2)) hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro t ht
      apply (hc v hv t ht).mul
      have hp : Continuous (fun u : ℝ => P u 0 v) := by unfold P r q; fun_prop
      exact (continuousAt_const.div (continuous_sqrt.continuousAt.comp hp.continuousAt)
        (sqrt_pos.mpr (P_pos ht (by norm_num) hv)).ne').continuousWithinAt)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using H

/-- Continuity of the actual calibration ratio at both parameter endpoints.
Use: converts strict interior monotonicity into the complete range and unique inverse theorem.
Article: jacobi, Theorem D.5.
Proof: apply dominated continuity to the two numerators and divide by the positive i_2². -/
theorem ratio_continuousOn : ContinuousOn ratio (Icc (0 : ℝ) 1) := by
  -- Positivity of the denominator is proved from the actual integrable weight.
  have hi := weighted_quadrature_continuous (fun _ _ => 1)
    (fun _ => measurable_const) (fun _ _ => continuousOn_const) (fun _ _ _ _ => by norm_num)
  simp only [one_mul] at hi
  have hk := weighted_quadrature_continuous L (fun _ => by unfold L; fun_prop)
    (fun _ _ => by unfold L; fun_prop) (fun t ht v hv => by
      have hL := L_bounds ht ⟨hv.1.le,hv.2.le⟩
      rw [abs_of_nonneg (hv.1.le.trans hL.1)]
      exact hL.2)
  exact (continuousOn_const.mul hk).div (continuousOn_const.mul (hi.pow 2))
    (fun t ht => by have h := i2_pos ht (by norm_num : (0 : ℝ) ∈ Icc 0 1); positivity)

/-- The zero-shape second quadrature has exact value two thirds.
Use: the upper endpoint of the ratio's range.
Article: jacobi, Theorem D.5.
Proof: integrate the derivative of -(2/3)sqrt(1-v³); no numerical quadrature is used. -/
theorem i2_zero : i2 0 0 = 2/3 := by
  -- The primitive is continuous on the closed interval and differentiable on its interior.
  have he (v : ℝ) : P 0 0 v=1-v^3 := by dsimp [P,r,q]; ring
  let F (v : ℝ) := -(2/3 : ℝ)*sqrt (1-v^3)
  have hd (v : ℝ) (hv : v ∈ Ioo 0 1) : HasDerivAt F (quadratureWeight 0 0 v) v := by
    have hp : 0 < 1-v^3 := by rw [← he]; exact P_pos (by norm_num) (by norm_num) hv
    have h := ((((hasDerivAt_id v).pow 3).const_sub 1).sqrt hp.ne').const_mul (-(2/3 : ℝ))
    convert h using 1
    · rfl
    · dsimp only [quadratureWeight,id_eq]
      norm_num only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one]
      rw [he]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (f := F) (by dsimp [F]; fun_prop) hd
    (quadratureWeight_integrable (by norm_num) (by norm_num))
  norm_num [F] at h
  exact h

/-- Exact elementary moments of the simple square-root endpoint weight.
Use: evaluates i_2(1), i_3(1) and hence the Young/elliptic transition ratio.
Article: jacobi, Theorem D.5.
Proof: explicit polynomial primitives in sqrt(1-v) give both rational values. -/
theorem endpointWeight_moments :
    (∫ v in (0 : ℝ)..1, v*endpointWeight v)=4/3 ∧
    (∫ v in (0 : ℝ)..1, v^2*endpointWeight v)=16/15 := by
  -- The square-root derivative is only used strictly inside the integration interval.
  let F (v : ℝ) := -2*sqrt (1-v)+(2/3 : ℝ)*sqrt (1-v)^3
  let G (v : ℝ) := -2*sqrt (1-v)+(4/3 : ℝ)*sqrt (1-v)^3-(2/5 : ℝ)*sqrt (1-v)^5
  have hs (v : ℝ) (hv : v ∈ Ioo 0 1) :=
    ((hasDerivAt_id v).const_sub 1).sqrt (sub_pos.mpr hv.2).ne'
  have hdF (v : ℝ) (hv : v ∈ Ioo 0 1) : HasDerivAt F (v*endpointWeight v) v := by
    have h := ((hs v hv).const_mul (-2)).add (((hs v hv).pow 3).const_mul (2/3 : ℝ))
    convert h using 1
    · rfl
    · dsimp only [endpointWeight,id_eq]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub]
      field_simp [(sqrt_pos.mpr (sub_pos.mpr hv.2)).ne']
      nlinarith [sq_sqrt (sub_nonneg.mpr hv.2.le)]
  have hdG (v : ℝ) (hv : v ∈ Ioo 0 1) : HasDerivAt G (v^2*endpointWeight v) v := by
    have h := (((hs v hv).const_mul (-2)).add (((hs v hv).pow 3).const_mul (4/3 : ℝ))).sub
      (((hs v hv).pow 5).const_mul (2/5 : ℝ))
    convert h using 1
    · rfl
    · dsimp only [endpointWeight,id_eq]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub]
      field_simp [(sqrt_pos.mpr (sub_pos.mpr hv.2)).ne']
      have hs2 := sq_sqrt (sub_nonneg.mpr hv.2.le)
      have hs4 := congrArg (fun z : ℝ => z^2) hs2
      nlinarith
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (f := F) (by dsimp [F]; fun_prop) hdF
    (endpointWeight_integrable.continuousOn_mul continuous_id.continuousOn)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (f := G) (by dsimp [G]; fun_prop) hdG
    (endpointWeight_integrable.continuousOn_mul (continuous_id.pow 2).continuousOn)
  norm_num [F] at h1
  norm_num [G] at h2
  exact ⟨h1,h2⟩

/-- Exact endpoint values of the actual elliptic ratio.
Use: guarantees an interior calibration parameter for every strict elliptic ratio.
Article: jacobi, Theorem D.5.
Proof: use the evaluated integrals and the endpoint identities L(0,v)=1 and L(1,v)=v. -/
theorem ratio_endpoints : ratio 0=1 ∧ ratio 1=2/5 := by
  -- At shape one the quadrature weight reduces to v/sqrt(1-v) off the null endpoints.
  have hweight : ∀ v ∈ Ioo (0 : ℝ) 1, quadratureWeight 1 0 v=v*endpointWeight v := by
    intro v hv
    rw [quadratureWeight_factor hv]
    have hr : r 1 0 v=v^2 := by dsimp [r,q]; ring
    rw [hr,sqrt_sq hv.1.le]
    field_simp
  have hi1 : i2 1 0=4/3 := by
    calc
      _ = ∫ v in (0 : ℝ)..1, v*endpointWeight v :=
        intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hweight
      _ = _ := endpointWeight_moments.1
  have hk0 : kappa 0=i2 0 0 := by simp [kappa,i2,L]
  have hk1 : kappa 1=16/15 := by
    calc
      _ = ∫ v in (0 : ℝ)..1, v^2*endpointWeight v := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro v hv
        change L 1 v*quadratureWeight 1 0 v = v^2*endpointWeight v
        rw [hweight v hv]
        dsimp [L]
        ring
      _ = _ := endpointWeight_moments.2
  norm_num [ratio,hk0,hk1,i2_zero,hi1]

/-- Strict decrease including both endpoints of the literal quadrature ratio.
Use: excludes spurious endpoint parameters and gives uniqueness in the full closed domain.
Article: jacobi, Theorem D.5.
Proof: combine dominated endpoint continuity with the proved strictly negative interior derivative. -/
theorem ratio_strictAntiOn_closed : StrictAntiOn ratio (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) ratio_continuousOn
  intro t ht
  rw [interior_Icc] at ht
  obtain ⟨d,hd,hn⟩ := ratio_hasDerivAt_neg ht
  rwa [hd.deriv]

/-- Every strict elliptic second-to-mass ratio has exactly one interior shape parameter.
Use: the parameter in the elliptic energy formula is well-defined without any numerical root certificate.
Article: jacobi, Theorem D.5.
Proof: the intermediate value theorem gives existence between the exact endpoints;
strict decrease gives uniqueness and excludes the endpoints. -/
theorem unique_ratio_parameter {z : ℝ} (hz : z ∈ Ioo (2/5 : ℝ) 1) :
    ∃! t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ ratio t=z := by
  -- Apply the theorem to the entire closed interval, then use the strict target inequalities.
  have hz' : z ∈ Icc (ratio 1) (ratio 0) := by
    rw [ratio_endpoints.1,ratio_endpoints.2]
    exact ⟨hz.1.le,hz.2.le⟩
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) ratio_continuousOn hz'
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h
    subst t
    rw [ratio_endpoints.1] at he
    linarith [hz.2])
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro h
    subst t
    rw [ratio_endpoints.2] at he
    linarith [hz.1])
  refine ⟨t,⟨⟨ht0,ht1⟩,he⟩,?_⟩
  intro u hu
  exact ratio_strictAntiOn_closed.injOn ⟨hu.1.1.le,hu.1.2.le⟩ ht (hu.2.trans he.symm)

end
end jacobi.Elliptic
