import nesterov.Corner.Algebra

/-! Exact necessity of the optimal corner wedge and the explicit regions. -/
namespace nesterov.Corner
noncomputable section
open Set Filter
open scoped Topology

theorem rationalXi_pos {K : ℕ} (hK : 3≤K) : 0<rationalXi K := by
  have hk : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hk3 : (3:ℝ)≤K := by exact_mod_cast hK
  have ha : 0<2*Real.pi/(K:ℝ) := by positivity
  have hb : 2*Real.pi/(K:ℝ)≤Real.pi := by
    apply (div_le_iff₀ hk).mpr
    nlinarith [Real.pi_pos]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hb ha
  rw [Real.cos_zero] at h
  exact sub_pos.mpr h

theorem exists_discrete_lt_one {a b : ℝ} (ha : 5/4<a) :
    ∃ K : ℕ,3≤K ∧ ratio 3 a b (rationalXi K)<1 := by
  have h : Tendsto (fun n : ℕ=>(5-4*a)+(4*a+b-6)*rationalXi (n+3)) atTop (𝓝 (5-4*a)) := by
    simpa only [mul_zero,add_zero] using
      tendsto_const_nhds.add (rationalXi_tendsto.const_mul (4*a+b-6))
  have hneg : 5-4*a<0 := by linarith
  obtain ⟨n,hn⟩ := (h.eventually (eventually_lt_nhds hneg)).exists
  refine ⟨n+3,by omega,?_⟩
  apply (ratio_lt_iff (rationalXi_mem (n+3)).2).mpr
  have hp := rationalXi_pos (show 3≤n+3 by omega)
  have hmul := mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0:ℝ)<2) hp) hn
  have he := wedge_difference a b (rationalXi (n+3))
  nlinarith

theorem cDisc_lt_one_of_deficit {a b : ℝ} (ha : 5/4<a) : cDisc 3 a b<1 := by
  obtain ⟨K,hK,hq⟩ := exists_discrete_lt_one (b:=b) ha
  exact (cDisc_le (rationalXi_mem_discreteSet hK)).trans_lt hq

theorem one_le_cDisc_iff {a b : ℝ} :
    1≤cDisc 3 a b ↔ a≤5/4 ∧ 7/2≤2*a+b := by
  constructor
  · intro h
    constructor
    · by_contra ha
      exact (not_lt_of_ge h) (cDisc_lt_one_of_deficit (lt_of_not_ge ha))
    · have hpi : cDisc 3 a b≤cpi 3 a b := (cDisc_endpoints _ _ _).trans (min_le_right _ _)
      unfold cpi at hpi
      linarith
  · rintro ⟨ha,hb⟩
    rw [(optimal_wedge_minima ha hb).2]

theorem one_le_cLag_iff {a b : ℝ} :
    1≤cLag 3 a b ↔ a≤5/4 ∧ 7/2≤2*a+b := by
  constructor
  · intro h
    exact one_le_cDisc_iff.mp (h.trans (cLag_le_cDisc _ _ _))
  · rintro ⟨ha,hb⟩
    rw [(optimal_wedge_minima ha hb).1]

theorem cDisc_le_one (a b : ℝ) : cDisc 3 a b≤1 := by
  simpa only [show (3:ℝ)/3=1 by norm_num] using (cDisc_endpoints 3 a b).trans (min_le_left _ _)

theorem cDisc_eq_one_iff {a b : ℝ} :
    cDisc 3 a b=1 ↔ a≤5/4 ∧ 7/2≤2*a+b := by
  rw [le_antisymm_iff]
  exact ⟨fun h=>one_le_cDisc_iff.mp h.2,fun h=>⟨cDisc_le_one _ _,one_le_cDisc_iff.mpr h⟩⟩

theorem cLag_eq_one_iff {a b : ℝ} :
    cLag 3 a b=1 ↔ a≤5/4 ∧ 7/2≤2*a+b := by
  constructor
  · intro h
    exact one_le_cLag_iff.mp h.ge
  · rintro ⟨ha,hb⟩
    exact (optimal_wedge_minima ha hb).1

theorem optimal_vertex (a b : ℝ) (h : a≤5/4 ∧ 7/2≤2*a+b) :
    a≤5/4 ∧ (a=5/4 → 1≤b) := by
  refine ⟨h.1,?_⟩
  intro ha
  rw [ha] at h
  linarith [h.2]

theorem beyond_wall_optimal {a b : ℝ} (ha : a≤0) (hb : 7/2-2*a≤b) :
    cLag 3 a b=1 ∧ cDisc 3 a b=1 :=
  optimal_wedge_minima (by linarith) (by linarith)

theorem flow_region_minimum {θ a b : ℝ} (hθ : 0≤θ) (hθ3 : θ≤3)
    (ha : a≤5*θ/12) (hb : 7*θ/6≤2*a+b) :
    min (Flow.cQ θ 2) (cLag θ a b)=θ/3 ∧
      min (Flow.cQ θ 2) (cDisc θ a b)=θ/3 := by
  rw [(flow_region_minima ha hb).1,(flow_region_minima ha hb).2]
  exact ⟨min_eq_right (cQ_ge_third hθ hθ3),min_eq_right (cQ_ge_third hθ hθ3)⟩

theorem alternating_region_minimum {θ a b : ℝ} (hθ : 0≤θ) (hθ3 : θ≤3)
    (hb : 2*a+b<7*θ/6) (hab : 5*a+2*b≤11*θ/4) :
    min (Flow.cQ θ 2) (cLag θ a b)=cpi θ a b ∧
      min (Flow.cQ θ 2) (cDisc θ a b)=cpi θ a b := by
  have hpi : cpi θ a b≤Flow.cQ θ 2 := by
    have h := cQ_ge_third hθ hθ3
    unfold cpi
    linarith
  rw [(alternating_region_minima hb hab).1,(alternating_region_minima hb hab).2]
  exact ⟨min_eq_right hpi,min_eq_right hpi⟩

end
end nesterov.Corner
