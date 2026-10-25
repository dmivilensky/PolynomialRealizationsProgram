import polyak.General.Regions.Polyak
import polyak.General.Regions.Contacts

/-! Article: Corollary D(a), Polyak's critical point is the K=3 contact on
the relative lag-one boundary. The closure assertion is proved by an actual
continuous curve of admissible subcritical tunings. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics Filter Set
open scoped Topology

private abbrev ScalarDomain := Ioo (0:ℝ) 1

private def scalarPolyak (s : ScalarDomain) : Tuning :=
  Tuning.ofOriginal ((1-(s:ℝ))^2) ((1+(s:ℝ))^2) 1 ((s:ℝ)^2)
    (sq_pos_of_pos (by linarith [s.property.2]))
    (by nlinarith [s.property.1]) (by norm_num) (sq_nonneg _)
    (by nlinarith [s.property.1,s.property.2])
    (by nlinarith [sq_pos_of_pos (show 0<1-(s:ℝ) by linarith [s.property.2])])

private theorem scalarPolyak_x (s : ScalarDomain) : (scalarPolyak s).x=(1-(s:ℝ))^2 := by
  simp only [scalarPolyak,Tuning.x,Tuning.ofOriginal,one_mul]
  field_simp [show 1+(s:ℝ)≠0 by linarith [s.property.1]]


private theorem scalarPolyak_continuous : Continuous scalarPolyak := by
  apply continuous_induced_rng.mpr
  change Continuous (fun s : ScalarDomain=>
    (((1+(s:ℝ))^2/(1-(s:ℝ))^2),1*(1+(s:ℝ))^2,(s:ℝ)^2))
  fun_prop (disch := intro s; exact ne_of_gt (sq_pos_of_pos (by linarith [s.property.2])))

private theorem tuning_ext {q p : Tuning} (hk : q.kappa=p.kappa) (hy : q.y=p.y)
    (hb : q.beta=p.beta) : q=p := by
  cases q; cases p; dsimp at hk hy hb
  subst_vars
  rfl

private theorem kappa_eq_y_div_x (q : Tuning) : q.kappa=q.y/q.x := by
  apply (eq_div_iff (ne_of_gt q.x_pos)).mpr
  rw [mul_comm]
  exact div_mul_cancel₀ _ (ne_of_gt q.kappa_pos)

private theorem eq_scalarPolyak (q : Tuning) (s : ScalarDomain)
    (hx : q.x=(1-(s:ℝ))^2) (hy : q.y=(1+(s:ℝ))^2) (hb : q.beta=(s:ℝ)^2) :
    q=scalarPolyak s := by
  apply tuning_ext
  · rw [kappa_eq_y_div_x q,kappa_eq_y_div_x (scalarPolyak s),scalarPolyak_x,hx,hy]
    simp only [scalarPolyak,Tuning.ofOriginal,one_mul]
  · simpa only [scalarPolyak,Tuning.ofOriginal,one_mul] using hy
  · exact hb

private theorem critical_scalar_in_closure : scalarPolyak
    ⟨Threshold.criticalQ,Threshold.criticalQ_pos,Threshold.criticalQ_lt_one⟩∈
    closure {q : Tuning | OmegaOne q} := by
  let s₀ : ScalarDomain := ⟨Threshold.criticalQ,Threshold.criticalQ_pos,Threshold.criticalQ_lt_one⟩
  let s : ℕ→ScalarDomain := fun n=>⟨Threshold.criticalQ*(1-((n:ℝ)+2)⁻¹),by
    constructor
    · apply mul_pos Threshold.criticalQ_pos
      have hh : ((n:ℝ)+2)⁻¹<1 := inv_lt_one_of_one_lt₀ (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
      linarith
    · have hh : 0<((n:ℝ)+2)⁻¹ := by positivity
      have hh' := mul_pos Threshold.criticalQ_pos hh
      nlinarith [Threshold.criticalQ_lt_one]⟩
  have hsub (n : ℕ) : (s n:ℝ)<Threshold.criticalQ := by
    dsimp [s]
    have hh : 0<Threshold.criticalQ*((n:ℝ)+2)⁻¹ := by positivity [Threshold.criticalQ_pos]
    linarith
  have hinv : Tendsto (fun n : ℕ=>((n:ℝ)+2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hs : Tendsto s atTop (𝓝 s₀) := by
    apply tendsto_subtype_rng.mpr
    have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1)).sub hinv).const_mul Threshold.criticalQ
    simpa only [sub_zero,mul_one,s,s₀] using hh
  apply mem_closure_of_tendsto (scalarPolyak_continuous.continuousAt.tendsto.comp hs)
  exact Eventually.of_forall (fun n=>(polyak_mem_omegaOne_iff_q (scalarPolyak (s n))
    (s n).property.1 (s n).property.2 (scalarPolyak_x (s n)) (by simp only [scalarPolyak,Tuning.ofOriginal,one_mul]) (by rfl)).mpr (hsub n))

/-- Polyak's critical point belongs to the actual relative boundary of Omega1. -/
theorem critical_polyak_on_omegaOne_boundary {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hκ : L/μ=Threshold.criticalKappa) :
    polyakTuning hμ hL∈frontier {q : Tuning | OmegaOne q} := by
  have hs : polyakQ μ L=Threshold.criticalQ := by
    rw [Dynamics.polyakQ_eq_conditionQ hμ hL]
    exact (Threshold.conditionQ_eq_critical_iff ((one_lt_div hμ).mpr hL)).mpr hκ
  obtain ⟨hx,hy,hb⟩ := polyakTuning_coordinates hμ hL
  have he := eq_scalarPolyak (polyakTuning hμ hL)
    ⟨Threshold.criticalQ,Threshold.criticalQ_pos,Threshold.criticalQ_lt_one⟩
    (by simpa only [hs] using hx) (by simpa only [hs] using hy) (by simpa only [hs] using hb)
  rw [isOpen_omegaOne.frontier_eq]
  refine ⟨?_,?_⟩
  · rw [he]; exact critical_scalar_in_closure
  · intro h
    have hh := (polyak_mem_omegaOne_iff_condition hμ hL).mp h
    linarith

/-- The critical lag-one symbol vanishes exactly at the three-cycle cosine. -/
theorem critical_polyak_three_contact {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hκ : L/μ=Threshold.criticalKappa) :
    (polyakTuning hμ hL).angle (rationalAngle 1 3)=Real.pi/3 := by
  have hs : polyakQ μ L=Threshold.criticalQ := by
    rw [Dynamics.polyakQ_eq_conditionQ hμ hL]
    exact (Threshold.conditionQ_eq_critical_iff ((one_lt_div hμ).mpr hL)).mpr hκ
  obtain ⟨hx,hy,hb⟩ := polyakTuning_coordinates hμ hL
  have hq := Threshold.criticalQ_sq_add
  have hi : Threshold.criticalQ*Threshold.criticalQ⁻¹=1 := mul_inv_cancel₀ (ne_of_gt Threshold.criticalQ_pos)
  have hu : (Threshold.criticalQ⁻¹-Threshold.criticalQ)/2=(1:ℝ)/2 := by nlinarith
  have he := polyak_completed_square (polyakTuning hμ hL) (Dynamics.polyakQ_pos hμ hL)
    (Dynamics.polyakQ_lt_one hμ hL) hx hy hb (-(1:ℝ)/2)
  rw [hs,hu] at he
  norm_num at he
  have hz : (polyakTuning hμ hL).L (-(1:ℝ)/2)=0 := by
    rw [(polyakTuning hμ hL).L_eq_Xi]
    have hh : 1+ -(1:ℝ)/2-(polyakTuning hμ hL).Xi (-1/2)=0 := by linarith
    rw [hh,mul_zero]
  have hcos : Real.cos (rationalAngle 1 3)= -(1:ℝ)/2 := by
    have he' : rationalAngle 1 3=Real.pi-Real.pi/3 := by dsimp [rationalAngle]; ring
    rw [he',Real.cos_pi_sub,Real.cos_pi_div_three]
    norm_num
  have hω := rationalAngle_mem (j:=1) (k:=3) (by norm_num) (by norm_num)
  have hh := angle_eq_half_of_L_zero (polyakTuning hμ hL) hω (by rwa [hcos])
  have hehalf : rationalAngle 1 3/2=Real.pi/3 := by dsimp [rationalAngle]; ring
  rw [hehalf] at hh
  exact hh

/-- Above the threshold the three-tongue inequality is genuinely strict. -/
theorem supercritical_polyak_three_strict {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hκ : Threshold.criticalKappa<L/μ) :
    (polyakTuning hμ hL).L (-(1:ℝ)/2)<0 := by
  let s := Dynamics.polyakQ μ L
  let u := (s⁻¹-s)/2
  have hs : 0<s := Dynamics.polyakQ_pos hμ hL
  have hs1 : s<1 := Dynamics.polyakQ_lt_one hμ hL
  have hcrit : Threshold.criticalQ<s := by
    dsimp [s]
    rw [Dynamics.polyakQ_eq_conditionQ hμ hL]
    exact (Threshold.critical_lt_conditionQ_iff ((one_lt_div hμ).mpr hL)).mpr hκ
  have hu : 0<u := by
    have hh : s<s⁻¹ := (mul_lt_mul_iff_left₀ hs).mp (by rw [inv_mul_cancel₀ (ne_of_gt hs)]; nlinarith)
    dsimp [u]; linarith
  have hu1 : u<(1:ℝ)/2 := by
    have hh : 0<(s-Threshold.criticalQ)*(s+Threshold.criticalQ+1) :=
      mul_pos (by linarith) (by linarith [Threshold.criticalQ_pos])
    have hi : s*s⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hs)
    have he := Threshold.criticalQ_sq_add
    have hneg : s*(s⁻¹-s-1)<0 := by nlinarith
    have hh' : s⁻¹-s-1<0 := neg_of_mul_neg_right hneg hs.le
    dsimp [u]
    linarith
  obtain ⟨hx,hy,hb⟩ := polyakTuning_coordinates hμ hL
  have he := polyak_completed_square (polyakTuning hμ hL) hs hs1 hx hy hb (-(1:ℝ)/2)
  change 2*u*(1+ -(1:ℝ)/2-(polyakTuning hμ hL).Xi (-(1:ℝ)/2))=(-(1:ℝ)/2+u)^2+2*u-1 at he
  have hfac : (-(1:ℝ)/2+u)^2+2*u-1=(u+3/2)*(u-1/2) := by ring
  rw [hfac] at he
  have hval : 1+ -(1:ℝ)/2-(polyakTuning hμ hL).Xi (-(1:ℝ)/2)<0 := by
    have hh : (u+3/2)*(u-1/2)<0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    rw [← he] at hh
    exact neg_of_mul_neg_right hh (by positivity)
  rw [(polyakTuning hμ hL).L_eq_Xi]
  exact mul_neg_of_pos_of_neg (mul_pos (sub_pos.mpr (polyakTuning hμ hL).x_lt_y)
    (sub_pos.mpr (polyakTuning hμ hL).beta_lt_one)) hval

/-- Polyak's tuning lies on both critical damping curves, as asserted in Part II. -/
theorem polyak_on_damping_curves {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    (polyakTuning hμ hL).x=(1-Real.sqrt (polyakTuning hμ hL).beta)^2 ∧
    (polyakTuning hμ hL).y=(1+Real.sqrt (polyakTuning hμ hL).beta)^2 := by
  obtain ⟨hx,hy,hb⟩ := polyakTuning_coordinates hμ hL
  rw [hb,Real.sqrt_sq (Dynamics.polyakQ_pos hμ hL).le]
  exact ⟨hx,hy⟩

end
end polyak.General.Regions
