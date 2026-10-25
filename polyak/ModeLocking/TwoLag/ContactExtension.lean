import polyak.ModeLocking.TwoLag.Extension
import polyak.ModeLocking.Regular.Endpoints

/-! The local factorization is an equality of genuine analytic real
extensions, so it transports the second jets of double contacts. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set Filter
open scoped Topology

def realFactor (q : Tuning) (K : ℕ) (a b x : ℝ) : ℝ :=
  a*(Real.sin (phase q 0 x)*(1-Real.cos x)*(1+(b/a)*W K (Real.cos x))/Real.sin x)

theorem analyticAt_Xi (q : Tuning) (c : ℝ) : AnalyticAt ℝ q.Xi c := by
  unfold Tuning.Xi
  fun_prop

theorem analyticAt_realFactor (q : Tuning) (K : ℕ) (a b : ℝ) {u : ℝ}
    (hu : u∈Ioo 0 Real.pi) : AnalyticAt ℝ (realFactor q K a b) u := by
  have hp := analyticAt_phase q 0 ⟨hu.1.le,hu.2.le⟩
  have hw := (analyticAt_W K (Real.cos u)).comp Real.analyticAt_cos
  exact analyticAt_const.mul
    ((((Real.analyticAt_sin.comp hp).mul (analyticAt_const.sub Real.analyticAt_cos)).mul
      (analyticAt_const.add (analyticAt_const.mul hw))).div Real.analyticAt_sin
        (Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2).ne')

theorem phase_zero_actual (q : Tuning) (ω : Frequency) : phase q 0 ω=q.angle ω := by
  simp only [phase, Geometry.jointAngle_actual q 0 ω.property,
    ←Geometry.shiftedCurve_apply, Geometry.shiftedCurve_zero, tuningCurve_apply]

theorem realFactor_positive (q : Tuning) (K : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0≤b)
    (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi) : 0<realFactor q K a b ω := by
  simpa only [realFactor, phase_zero_actual] using factor_pos q K ha hb ω hω

theorem extension_eventually_factor (q : Tuning) {K : ℕ} (hK : 0<K) {a b u : ℝ}
    (ha : 0<a) (hb : 0≤b) (hu : u∈Ioo 0 Real.pi) :
    extension q 0 K a b =ᶠ[𝓝 u]
      fun x=>realFactor q K a b x*(q.Xi (Real.cos x)-Psi K (b/a) (Real.cos x)) := by
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
  let ω : Frequency := ⟨x,hx.1.le,hx.2.le⟩
  have h := symbol_factor q hK ha hb ω hx
  change extension q 0 K a b ω=realFactor q K a b ω*
    (q.Xi (Real.cos (ω : ℝ))-Psi K (b/a) (Real.cos (ω : ℝ)))
  rw [extension_actual, Geometry.shiftedCurve_zero]
  simpa only [symbol, realFactor, phase_zero_actual] using h

/-- Negative second derivative of the lag symbol is exactly positive
second derivative of the rational gap at a contact. -/
theorem contact_curvature_iff (q : Tuning) {K : ℕ} (hK : 0<K) {a b : ℝ}
    (ha : 0<a) (hb : 0≤b) (ω : Frequency) (hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi)
    (hvalue : q.Xi (Real.cos (ω : ℝ))=Psi K (b/a) (Real.cos (ω : ℝ)))
    (hslope : deriv q.Xi (Real.cos (ω : ℝ))=deriv (Psi K (b/a)) (Real.cos (ω : ℝ))) :
    (deriv^[2] (extension q 0 K a b) ω<0 ↔
      0<deriv^[2] (fun c=>Psi K (b/a) c-q.Xi c) (Real.cos (ω : ℝ))) := by
  let g := fun c=>q.Xi c-Psi K (b/a) c
  have hc : Real.cos (ω : ℝ)∈Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hg := (analyticAt_Xi q (Real.cos (ω : ℝ))).sub (analyticAt_Psi K (div_nonneg hb ha.le) hc)
  have h0 : g (Real.cos (ω : ℝ))=0 := sub_eq_zero.mpr hvalue
  have h1 : deriv g (Real.cos (ω : ℝ))=0 := by
    have h := ((analyticAt_Xi q (Real.cos (ω : ℝ))).differentiableAt.hasDerivAt.sub
      (analyticAt_Psi K (div_nonneg hb ha.le) hc).differentiableAt.hasDerivAt).deriv
    change deriv g (Real.cos (ω : ℝ))=_ at h
    rw [h,hslope,sub_self]
  have hlocal := extension_eventually_factor q hK ha hb hω
  have heq := hlocal.iteratedDeriv_eq 2
  simp only [iteratedDeriv_eq_iterate] at heq
  rw [heq]
  have hh := second_contact_sign (analyticAt_realFactor q K a b hω).contDiffAt hg.contDiffAt h0 h1
    (realFactor_positive q K ha hb ω hω) (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'
  change (deriv^[2] (fun x=>realFactor q K a b x*g (Real.cos x)) ω<0 ↔
    deriv^[2] g (Real.cos (ω : ℝ))<0) at hh
  have hneg : (fun c=>Psi K (b/a) c-q.Xi c)=fun c=>-g c := by funext c;dsimp [g];ring
  change (deriv^[2] (fun x=>realFactor q K a b x*g (Real.cos x)) ω<0 ↔ _)
  rw [hh,hneg]
  have hd : deriv^[2] (fun c=>-g c) (Real.cos (ω : ℝ)) = -deriv^[2] g (Real.cos (ω : ℝ)) := by
    rw [←iteratedDeriv_eq_iterate, iteratedDeriv_fun_neg, iteratedDeriv_eq_iterate]
  rw [hd]
  exact neg_pos.symm


theorem extension_second_endpoint (q : Tuning) (s : ℝ) (K : ℕ) (a b : ℝ) :
    deriv^[2] (extension q s K a b) 0= -endpointMoment q K a b := by
  rw [←iteratedDeriv_eq_iterate]
  unfold extension
  rw [iteratedDeriv_fun_add
    (contDiffAt_const.mul (analyticAt_lagExtension q s 1 ⟨le_rfl,Real.pi_pos.le⟩).contDiffAt)
    (contDiffAt_const.mul (analyticAt_lagExtension q s (-(K : ℤ)) ⟨le_rfl,Real.pi_pos.le⟩).contDiffAt),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate, lagExtension_second_zero, Int.cast_one, Int.cast_neg,
    Int.cast_natCast]
  unfold endpointMoment
  ring

theorem endpoint_curvature_iff (q : Tuning) {K : ℕ} (hK : 1≤K) {a b : ℝ}
    (ha : 0<a) (hb : 0≤b) :
    (deriv^[2] (extension q 0 K a b) 0<0 ↔ q.Xi 1<Psi K (b/a) 1) := by
  rw [extension_second_endpoint, neg_lt_zero, endpointMoment_pos_iff q hK ha hb]

end polyak.ModeLocking.TwoLag
