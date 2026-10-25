import polyak.General.Regions.PhaseLocking
import polyak.General.Regions.Tangency
import polyak.General.Regions.TongueCriteria

/-! Article: Theorem A(iii), Corollary C(a). Exact tangencies and the boundary
of actual convergence, distinguished from a statement merely about rho=1. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics Filter Set
open scoped Topology

/-- Weak lag-one positivity is exactly the nonstrict angle condition. -/
theorem weak_omegaOne_angle_ge (q : Tuning) (hq : WeakOmegaOne q)
    {ω : ℝ} (hω : ω∈Ioc (0:ℝ) Real.pi) : ω/2≤q.angle ω := by
  by_cases hπ : ω=Real.pi
  · subst ω; rw [q.angle_pi]; linarith [Real.pi_pos]
  have hω' : ω∈Ioo (0:ℝ) Real.pi := ⟨hω.1,lt_of_le_of_ne hω.2 hπ⟩
  have hh : ω/2∈Ioo (0:ℝ) Real.pi := ⟨by linarith [hω.1],by linarith [hω.2,Real.pi_pos]⟩
  have hc := hq (Real.cos ω) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  rw [q.L_eq_Xi] at hc
  have hp : 0<(q.y-q.x)*(1-q.beta) := mul_pos (sub_pos.mpr q.x_lt_y) (sub_pos.mpr q.beta_lt_one)
  have hxi : q.Xi (Real.cos ω)≤1+Real.cos ω := by
    have := nonneg_of_mul_nonneg_right hc hp
    linarith
  have hcot : Real.cos (q.angle ω)/Real.sin (q.angle ω)≤Real.cos (ω/2)/Real.sin (ω/2) := by
    rw [q.cot_angle hω',cot_half hω']
    exact div_le_div_of_nonneg_right hxi (Real.sin_pos_of_pos_of_lt_pi hω'.1 hω'.2).le
  by_contra h
  have he := (cot_strictAnti hh (q.angle_mem hω')).mpr (lt_of_not_ge h)
  exact (not_lt_of_ge hcot) he

/-- At an interior zero the angle gap vanishes exactly. -/
theorem angle_eq_half_of_L_zero (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi)
    (hz : q.L (Real.cos ω)=0) : q.angle ω=ω/2 := by
  have hp : 0<(q.y-q.x)*(1-q.beta) := mul_pos (sub_pos.mpr q.x_lt_y) (sub_pos.mpr q.beta_lt_one)
  have hxi : q.Xi (Real.cos ω)=1+Real.cos ω := by
    rw [q.L_eq_Xi] at hz
    have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
    linarith
  have hc : Real.cos (q.angle ω)/Real.sin (q.angle ω)=Real.cos (ω/2)/Real.sin (ω/2) := by
    rw [q.cot_angle hω,cot_half hω,hxi]
  have hh : ω/2∈Ioo (0:ℝ) Real.pi := ⟨by linarith [hω.1],by linarith [hω.2,Real.pi_pos]⟩
  rcases lt_trichotomy (q.angle ω) (ω/2) with h|h|h
  · have he := (cot_strictAnti hh (q.angle_mem hω)).mpr h
    rw [hc] at he
    exact False.elim (lt_irrefl _ he)
  · exact h
  · have he := (cot_strictAnti (q.angle_mem hω) hh).mpr h
    rw [hc] at he
    exact False.elim (lt_irrefl _ he)

/-- Corollary C(a): the vertex's arccos is an actual minimizing tangency frequency. -/
theorem frontier_tangency_angle {q : Tuning}
    (hq : q∈frontier {p : Tuning | OmegaOne p}) :
    let ω := Real.arccos (vertex q)
    ω∈Ioo (0:ℝ) Real.pi ∧ q.angle ω=ω/2 ∧
      IsMinOn (fun u=>q.angle u-u/2) (Ioc (0:ℝ) Real.pi) ω := by
  obtain ⟨_,hv,hz,_⟩ := frontier_omegaOne_tangent hq
  have hω : Real.arccos (vertex q)∈Ioo (0:ℝ) Real.pi :=
    ⟨Real.arccos_pos.mpr hv.2,Real.arccos_lt_pi.mpr hv.1⟩
  have he : q.angle (Real.arccos (vertex q))=Real.arccos (vertex q)/2 := by
    apply angle_eq_half_of_L_zero q hω
    simpa only [Real.cos_arccos hv.1.le hv.2.le] using hz
  refine ⟨hω,he,?_⟩
  intro u hu
  change q.angle (Real.arccos (vertex q))-Real.arccos (vertex q)/2≤q.angle u-u/2
  rw [he,sub_self]
  exact sub_nonneg.mpr (weak_omegaOne_angle_ge q
    (closure_omegaOne_subset_weak (frontier_subset_closure hq)) hu)

/-- The actual convergence region, with all finite dimensions, objectives and starts. -/
def ConvergesAll (q : Tuning) : Prop := ∀ d : ℕ,
  ∀ f : EuclideanSpace ℝ (Fin d)→ℝ,SmoothStronglyConvex q.x q.y f→
  ∀ a,(∀ y,f a≤f y)→∀ x₀,Tendsto (iterate (gradient f) 1 q.beta x₀) atTop (𝓝 a)

theorem omegaOne_subset_convergesAll : {q : Tuning | OmegaOne q}⊆{q : Tuning | ConvergesAll q} := by
  intro q hq d f hf a hmin x₀
  exact omegaOne_converges q hq hf a hmin x₀

/-- A rational feasible atom refutes actual convergence by a single R3 trajectory. -/
theorem not_convergesAll_of_rational_phase (q : Tuning) {j k : ℕ}
    (hcop : j.Coprime k) (hj : 1≤j) (hjk : 2*j<k)
    (hphase : q.angle (rationalAngle j k)≤Real.pi/k) : ¬ConvergesAll q := by
  intro hall
  obtain ⟨f,hf,x₀,hx,c₀,hc,_,hb,_⟩ := exists_planar_startup q
    (cosineFrequency (rationalAngle j k)) ((single_harmonic_feasible_iff q hcop hj hjk).mpr hphase)
  have hmin : ∀ y,f 0≤f y := (hf.toSmoothStronglyConvex.minimizer_iff 0).mpr hf.gradient_zero
  have ht := (hall 3 f hf.toSmoothStronglyConvex 0 hmin x₀).norm
  simp only [norm_zero] at ht
  have hle : c₀*‖x₀‖≤0 := ge_of_tendsto ht (Eventually.of_forall hb)
  have hp : 0<c₀*‖x₀‖ := mul_pos hc (norm_pos_iff.mpr hx)
  linarith

/-- Theorem A(iii), the locked contact lies on the boundary of actual convergence. -/
theorem phase_locked_on_convergence_boundary (q : Tuning) {k : ℕ} (hk : 2<k)
    (hq : q∈closure {p : Tuning | OmegaOne p})
    (htouch : q.angle (rationalAngle 1 k)=Real.pi/k) :
    q∈frontier {p : Tuning | ConvergesAll p} := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨closure_mono omegaOne_subset_convergesAll hq,subset_closure ?_⟩
  exact not_convergesAll_of_rational_phase q (by simp) (by norm_num) (by omega) htouch.le

end
end polyak.General.Regions
