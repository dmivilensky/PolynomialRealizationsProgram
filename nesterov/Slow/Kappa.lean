import nesterov.Slow.Consequences

/-! The source condition-number variable κ and the reciprocal-square-root
endpoint parameter describe exactly the same rate coefficients. -/
namespace nesterov.Slow
noncomputable section
open Filter Set
open scoped Topology

def epsilon (κ : ℝ) : ℝ := 1/Real.sqrt κ

theorem epsilon_tendsto : Tendsto epsilon atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun κ : ℝ=>1/Real.sqrt κ) atTop (𝓝 0)
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
    exact one_div_pos.mpr (Real.sqrt_pos.mpr hκ)

theorem epsilon_sq {κ : ℝ} (hκ : 0≤κ) : epsilon κ^2=1/κ := by
  rw [epsilon,div_pow,Real.sq_sqrt hκ,one_pow]

theorem coefficient_kappa {κ R : ℝ} (_hκ : 0<κ) :
    (1-R)/epsilon κ=Real.sqrt κ*(1-R) := by
  unfold epsilon
  field_simp

 def conditionNumber (ε : ℝ) : ℝ := 1/ε^2

 theorem conditionNumber_tendsto : Tendsto conditionNumber (𝓝[>] (0:ℝ)) atTop := by
  change Tendsto (fun ε : ℝ=>1/ε^2) (𝓝[>] (0:ℝ)) atTop
  simpa only [one_div,inv_pow,Function.comp_def] using
    (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp (tendsto_inv_nhdsGT_zero (𝕜:=ℝ))

 theorem epsilon_conditionNumber {ε : ℝ} (hε : 0<ε) : epsilon (conditionNumber ε)=ε := by
  unfold epsilon conditionNumber
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,Real.sqrt_sq_eq_abs,abs_of_pos hε]
  field_simp

 theorem map_epsilon_atTop : map epsilon atTop=𝓝[>] (0:ℝ) := by
  apply le_antisymm epsilon_tendsto
  have heq : (fun ε : ℝ=>epsilon (conditionNumber ε))=ᶠ[𝓝[>] (0:ℝ)] id := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact epsilon_conditionNumber hε
  have hm : map epsilon (map conditionNumber (𝓝[>] (0:ℝ)))=𝓝[>] (0:ℝ) := by
    rw [map_map]
    exact (map_congr heq).trans map_id
  rw [←hm]
  exact map_mono conditionNumber_tendsto

 theorem epsilon_limsup (f : ℝ→EReal) :
    limsup (fun κ=>f (epsilon κ)) atTop=limsup f (𝓝[>] (0:ℝ)) := by
  change limsup (f∘epsilon) atTop=_
  rw [limsup_comp,map_epsilon_atTop]

 theorem epsilon_liminf (f : ℝ→EReal) :
    liminf (fun κ=>f (epsilon κ)) atTop=liminf f (𝓝[>] (0:ℝ)) := by
  change liminf (f∘epsilon) atTop=_
  rw [liminf_comp,map_epsilon_atTop]

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

def kappaCoefficient (κ : ℝ) : ℝ :=
  Real.sqrt κ*(1-Rates.rate (F.method (epsilon κ)) (1/κ) 1)

def kappaQuadraticCoefficient (κ : ℝ) : ℝ :=
  Real.sqrt κ*(1-Rates.quadraticRate (F.method (epsilon κ)) (1/κ) 1)

theorem kappa_coefficient_eq {κ : ℝ} (hκ : 0<κ) : F.kappaCoefficient κ=F.coefficient (epsilon κ) := by
  rw [coefficient,epsilon_sq hκ.le,coefficient_kappa hκ]
  rfl

theorem kappa_quadratic_coefficient_eq {κ : ℝ} (hκ : 0<κ) :
    F.kappaQuadraticCoefficient κ=F.quadraticCoefficient (epsilon κ) := by
  rw [quadraticCoefficient,epsilon_sq hκ.le,coefficient_kappa hκ]
  rfl

 theorem kappa_limsup_eq :
    limsup (fun κ=>(F.kappaCoefficient κ:EReal)) atTop=
      limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ)) := by
  rw [←epsilon_limsup]
  apply limsup_congr
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  rw [F.kappa_coefficient_eq hκ]

 theorem kappa_liminf_eq :
    liminf (fun κ=>(F.kappaCoefficient κ:EReal)) atTop=
      liminf (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ)) := by
  rw [←epsilon_liminf]
  apply liminf_congr
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  rw [F.kappa_coefficient_eq hκ]

 theorem kappa_quadratic_limsup_eq :
    limsup (fun κ=>(F.kappaQuadraticCoefficient κ:EReal)) atTop=
      limsup (fun ε=>(F.quadraticCoefficient ε:EReal)) (𝓝[>] (0:ℝ)) := by
  rw [←epsilon_limsup]
  apply limsup_congr
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  rw [F.kappa_quadratic_coefficient_eq hκ]

theorem kappa_coefficient_eventually_le {a : ℝ} (ha : Flow.cF θ y<a) :
    ∀ᶠ κ in atTop,F.kappaCoefficient κ≤a := by
  filter_upwards [epsilon_tendsto.eventually (F.coefficient_eventually_le ha),
    eventually_gt_atTop (0:ℝ)] with κ hκ hp
  simpa only [F.kappa_coefficient_eq hp] using hκ

theorem kappa_limsup_coefficient_le :
    limsup (fun κ=>(F.kappaCoefficient κ:EReal)) atTop≤(Flow.cF θ y:EReal) := by
  by_contra h
  obtain ⟨a,ha,halim⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have he : ∀ᶠ κ in atTop,(F.kappaCoefficient κ:EReal)≤(a:EReal) := by
    filter_upwards [F.kappa_coefficient_eventually_le (EReal.coe_lt_coe_iff.mp ha)] with κ hκ
    exact EReal.coe_le_coe_iff.mpr hκ
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) he)) halim

theorem kappa_quadratic_limsup_coefficient_le :
    limsup (fun κ=>(F.kappaQuadraticCoefficient κ:EReal)) atTop≤(Flow.cQ θ y:EReal) := by
  by_contra h
  obtain ⟨a,ha,halim⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have he : ∀ᶠ κ in atTop,(F.kappaQuadraticCoefficient κ:EReal)≤(a:EReal) := by
    filter_upwards [epsilon_tendsto.eventually (F.quadratic_coefficient_eventually_le
      (EReal.coe_lt_coe_iff.mp ha)),eventually_gt_atTop (0:ℝ)] with κ hκ hp
    apply EReal.coe_le_coe_iff.mpr
    simpa only [F.kappa_quadratic_coefficient_eq hp,quadraticCoefficient] using hκ
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) he)) halim

theorem kappa_nonlinear_optimal_ceiling :
    limsup (fun κ=>(F.kappaCoefficient κ:EReal)) atTop≤(Real.sqrt (y/2):EReal) :=
  F.kappa_limsup_coefficient_le.trans (EReal.coe_le_coe_iff.mpr (Flow.cF_le_optimal F.step_pos))

theorem kappa_necessary_slow_data
    (h : (1:EReal)≤liminf (fun κ=>(F.kappaCoefficient κ:EReal)) atTop) :
    3≤θ ∧ θ-1≤y ∧ 2≤θ-1 ∧ 2≤y := by
  have hr : 1≤Flow.cF θ y := EReal.coe_le_coe_iff.mp
    ((h.trans Filter.liminf_le_limsup).trans F.kappa_limsup_coefficient_le)
  have hh := (Flow.le_cF_iff (show (0:ℝ)≤1 by norm_num) θ y).mp hr
  norm_num at hh
  exact ⟨hh.1,by linarith [hh.2],by linarith,by linarith [hh.1,hh.2]⟩

 theorem kappa_pareto_ceiling :
    ∃ θ' : ℝ,2*Real.sqrt y≤θ' ∧ θ'≤3*Real.sqrt (y/2) ∧
      limsup (fun κ=>(F.kappaQuadraticCoefficient κ:EReal)) atTop≤(Flow.cQ θ' y:EReal) ∧
      limsup (fun κ=>(F.kappaCoefficient κ:EReal)) atTop≤((θ'/3:ℝ):EReal) ∧
      Flow.cF θ' y=θ'/3 := by
  simpa only [F.kappa_limsup_eq,F.kappa_quadratic_limsup_eq] using F.pareto_ceiling

 theorem kappa_critical_ceiling (hθ : θ=2*Real.sqrt y) :
    limsup (fun κ=>(F.kappaCoefficient κ:EReal)) atTop≤((2*Real.sqrt y/3:ℝ):EReal) := by
  rw [F.kappa_limsup_eq]
  exact F.critical_ceiling hθ

end SecondOrderFamily
end
end nesterov.Slow
