import «2610.05164v2».Calibration.ContactPotential

/-!
Article: 2610.05164v2, Theorem 3.2.
The strict comparison of the two reference filters in Appendix D.
Use: `«2610.05164v2».Calibration.ReferenceData.filter_reflection_strict` feeds
`«2610.05164v2».Calibration.ReferenceData.filter_order_coordinate` (filter order coordinate).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma` — 2610.05164v2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Comparison
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
The stated quantitative bound `R.referenceSpeed.X 0 < 0`.

Use: `«2610.05164v2».Calibration.ReferenceData.X_two_positive` uses this bound to establish the
stated quantitative bound `0 < R.referenceSpeed.X 2`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.X_one`,
`«2610.05164v2».PrescribedSpeed.SpeedData.X_strictMono` with the arguments shown in the proof.
-/
theorem X_zero_negative : R.referenceSpeed.X 0 < 0 := by
  simpa only [R.X_one] using R.referenceSpeed.X_strictMono
    (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 2) (by norm_num) (by norm_num : (0:ℝ)<1)

/--
Monotonicity in increasing order: `MonotoneOn R.density (Iic (0:ℝ))`.

Use: `«2610.05164v2».Calibration.ReferenceData.density_shift_order` uses this assertion to
establish the stated quantitative bound `R.density t ≤ R.density (t-2*x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `x ≤ R.referenceSpeed.X 0` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem density_mono_left : MonotoneOn R.density (Iic (0:ℝ)) := by
  -- Separate `x ≤ R.referenceSpeed.X 0` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  intro x hx y hy hxy
  by_cases hl : x ≤ R.referenceSpeed.X 0
  · have hz := R.referenceSpeed.density_zero_outside R.k
      (x := x) (fun hi => (not_lt_of_ge hl) hi.1)
    change R.density x=0 at hz
    rw [hz]
    exact R.density_properties.2.1 y
  · exact R.density_strictMono_left.monotoneOn ⟨(not_le.mp hl).le,hx⟩
      ⟨(not_le.mp hl).le.trans hxy,hy⟩ hxy

/--
The stated quantitative bound `R.density t ≤ R.density (t-2*x)`.

Use: `«2610.05164v2».Calibration.ReferenceData.filter_reflection_strict` uses this bound to
establish the stated quantitative bound `R.filter hσ x < R.filter hσ (-x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `t-2*x ≤ 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem density_shift_order {x t : ℝ} (hx : x ≤ 0) (ht : t ≤ x) :
    R.density t ≤ R.density (t-2*x) := by
  by_cases hs : t-2*x ≤ 0
  · exact R.density_mono_left (ht.trans hx) hs (by linarith)
  · have hpos : 0 < t-2*x := lt_of_not_ge hs
    calc R.density t ≤ R.density (-(t-2*x)) :=
          R.density_mono_left (a := t) (b := -(t-2*x)) (ht.trans hx) (by change -(t-2*x) ≤ 0; linarith) (by linarith)
         _ = R.density (t-2*x) := R.density_reflection _

/--
The stated quantitative bound `R.filter hσ x < R.filter hσ (-x)`.

Use: `«2610.05164v2».Calibration.ReferenceData.filter_order_coordinate` uses this bound to
establish the stated quantitative bound `(R.referenceSpeed.q x < 1 → R.filter hσ x < R.filter
hσ (-x)) ∧ (1 ≤ R.referenceSpeed.q x → R.filter hσ (-x) ≤ R.filter hσ x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.filter_c1`,
`«2610.05164v2».Calibration.ReferenceData.density_continuous`,
`«2610.05164v2».Calibration.ReferenceData.filter_derivative` with the arguments shown in the
proof.
-/
theorem filter_reflection_strict {x : ℝ} (hx : x ∈ Ioo (R.referenceSpeed.X 0) 0) :
    R.filter hσ x < R.filter hσ (-x) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.filter_c1`,
  -- `«2610.05164v2».Calibration.ReferenceData.density_continuous`,
  -- `«2610.05164v2».Calibration.ReferenceData.filter_derivative` with the arguments shown in
  -- the proof.
  let a := R.referenceSpeed.X 0+2*x
  let z := max (R.referenceSpeed.X 0) (2*x)
  let u := fun t => R.filter hσ (t-2*x)-R.filter hσ t
  let c := fun t => 2+σ*(R.filter hσ (t-2*x)+R.filter hσ t)
  let e := fun t => R.k*(R.density (t-2*x)-R.density t)
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous c := continuous_const.add
    ((((R.filter_c1 hσ).continuous.comp (continuous_id.sub continuous_const)).add
      (R.filter_c1 hσ).continuous).const_mul σ)
  -- Establish continuity he before using the function at limits or in calculus arguments.
  have he : Continuous e := ((R.density_continuous.comp
    (continuous_id.sub continuous_const)).sub R.density_continuous).const_mul R.k
  have hu : ∀ t, HasDerivAt u (-c t*u t+e t) t := by
    intro t
    have hs : HasDerivAt (fun t : ℝ => t-2*x) 1 t := by
      convert! (hasDerivAt_id t).sub_const (2*x) using 1
    convert! ((R.filter_derivative hσ (t-2*x)).comp t hs).sub
      (R.filter_derivative hσ t) using 1
    dsimp only [c,u,e]
    ring
  have h0 : u a=0 := by
    dsimp only [u,a]
    rw [show R.referenceSpeed.X 0+2*x-2*x=R.referenceSpeed.X 0 by ring,
      R.filter_zero_left hσ le_rfl,R.filter_zero_left hσ (by linarith [hx.2])]
    ring
  have hux := variation_of_constants hc he hu h0 x
  have hz : z < x := max_lt hx.1 (by linarith [hx.2])
  have haz : a ≤ z := (show a ≤ R.referenceSpeed.X 0 by dsimp [a]; linarith [hx.2]).trans
    (le_max_left _ _)
  let φ := fun t => exp (primitive c t)*e t
  -- Establish continuity hφ before using the function at limits or in calculus arguments.
  have hφ : Continuous φ := (Real.continuous_exp.comp (primitive_c1 hc).continuous).mul he
  have hp : 0 < ∫ t in z..x, φ t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hφ.intervalIntegrable z x) _ hz
    intro t ht
    have ht0 : t ∈ Icc (R.referenceSpeed.X 0) 0 :=
      ⟨(le_max_left _ _).trans ht.1.le,ht.2.le.trans hx.2.le⟩
    have hs0 : -(t-2*x) ∈ Icc (R.referenceSpeed.X 0) 0 := by
      constructor
      · linarith [ht0.1,ht.2]
      · linarith [(le_max_right (R.referenceSpeed.X 0) (2*x)).trans ht.1.le]
    have hm := R.density_strictMono_left ht0 hs0 (by linarith [ht.2])
    rw [R.density_reflection] at hm
    exact mul_pos (exp_pos _) (mul_pos R.k_positive (sub_pos.mpr hm))
  have hn : ∀ t ∈ Icc a x, 0 ≤ φ t := by
    intro t ht
    exact mul_nonneg (exp_pos _).le (mul_nonneg R.k_positive.le
      (sub_nonneg.mpr (R.density_shift_order hx.2.le ht.2)))
  have hm : (∫ t in z..x, φ t) ≤ ∫ t in a..x, φ t :=
    intervalIntegral.integral_mono_interval haz hz.le le_rfl
      ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hn t ⟨ht.1.le,ht.2⟩))
      (hφ.intervalIntegrable a x)
  have hp' : 0 < u x := by
    rw [hux]
    exact mul_pos (exp_pos _) (hp.trans_le hm)
  change 0 < R.filter hσ (x-2*x)-R.filter hσ x at hp'
  rw [show x-2*x= -x by ring] at hp'
  exact sub_pos.mp hp'

end
end «2610.05164v2».Calibration.ReferenceData
