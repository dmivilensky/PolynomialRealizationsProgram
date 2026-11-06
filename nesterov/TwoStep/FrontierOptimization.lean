import nesterov.Flow.Supporting
import nesterov.Flow.LevelSets
import nesterov.TwoStep.BoundaryQuadratic

/-! The exact optimization and componentwise arc geometry in frontier(iii,iv). -/
namespace nesterov.TwoStep
noncomputable section
open Set

def frontierStep (τ : ℝ) : ℝ := 4/(1+2*τ)
def bulkConstantSet (τ : ℝ) : Set ℝ :=
  {a | ∃ θ y : ℝ,0<θ ∧ 0<y ∧ y*(1+2*τ)<4 ∧ a=Flow.cF θ y}

theorem frontierStep_pos {τ : ℝ} (hτ : 0≤τ) : 0<frontierStep τ := by
  unfold frontierStep
  positivity

theorem margin_le_iff_frontierStep {τ y : ℝ} (hτ : 0≤τ) :
    y*(1+2*τ)≤4 ↔ y≤frontierStep τ := by
  exact (le_div_iff₀ (by linarith : 0<1+2*τ)).symm

theorem margin_lt_iff_frontierStep {τ y : ℝ} (hτ : 0≤τ) :
    y*(1+2*τ)<4 ↔ y<frontierStep τ := by
  exact (lt_div_iff₀ (by linarith : 0<1+2*τ)).symm

theorem frontierStep_lt_two {τ : ℝ} (hτ : 1/2<τ) : frontierStep τ<2 := by
  unfold frontierStep
  exact (div_lt_iff₀ (by linarith : 0<1+2*τ)).mpr (by linarith)

theorem cQ_mono_step (θ : ℝ) {y Y : ℝ} (hy : y≤Y) : Flow.cQ θ y≤Flow.cQ θ Y := by
  obtain ⟨hh,hd⟩ := (Flow.le_cQ_iff θ y (Flow.cQ θ y)).mp le_rfl
  exact (Flow.le_cQ_iff θ Y (Flow.cQ θ y)).mpr ⟨hh,by unfold Flow.delta at hd ⊢;linarith⟩

theorem cF_mono_step (θ : ℝ) {y Y : ℝ} (hy : y≤Y) : Flow.cF θ y≤Flow.cF θ Y :=
  min_le_min_left _ (cQ_mono_step θ hy)

theorem bulk_constant_strict_upper {θ y τ : ℝ} (hy : 0<y) (hτ : 0≤τ)
    (hmargin : y*(1+2*τ)<4) : Flow.cF θ y<Real.sqrt (frontierStep τ/2) := by
  exact (Flow.cF_le_optimal hy).trans_lt (Real.sqrt_lt_sqrt (by positivity)
    (by linarith [(margin_lt_iff_frontierStep hτ).mp hmargin]))

theorem bulk_constants_isLUB {τ : ℝ} (hτ : 0≤τ) :
    IsLUB (bulkConstantSet τ) (Real.sqrt (frontierStep τ/2)) := by
  have hY := frontierStep_pos hτ
  have hmax : 0<Real.sqrt (frontierStep τ/2) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · rintro a ⟨θ,y,_,hy,hm,rfl⟩
    exact (bulk_constant_strict_upper hy hτ hm).le
  · intro b hb
    by_contra hh
    have hlt : max b 0<Real.sqrt (frontierStep τ/2) := max_lt (lt_of_not_ge hh) hmax
    obtain ⟨c,hc,hcm⟩ := exists_between hlt
    have hc0 : 0<c := (le_max_right b 0).trans_lt hc
    have hbc : b<c := (le_max_left b 0).trans_lt hc
    have hs := Real.sq_sqrt (show 0≤frontierStep τ/2 by positivity)
    have hym : 2*c^2<frontierStep τ := by
      have hh := mul_self_lt_mul_self hc0.le hcm
      nlinarith
    have hcf : Flow.cF (3*c) (2*c^2)=c := by
      have hh := Flow.cF_at_nonlinear_optimal (m:=2*c^2) (mul_pos (by norm_num) (sq_pos_of_pos hc0))
      have hsqrt : Real.sqrt ((2*c^2)/2)=c := by rw [show (2*c^2)/2=c^2 by ring,Real.sqrt_sq hc0.le]
      simpa only [hsqrt] using hh
    have hmem : c∈bulkConstantSet τ :=
      ⟨3*c,2*c^2,by positivity,by positivity,
        (margin_lt_iff_frontierStep hτ).mpr hym,hcf.symm⟩
    exact (not_lt_of_ge (hb hmem)) hbc

theorem bulk_supremum_not_attained {τ : ℝ} (hτ : 0≤τ) :
    Real.sqrt (frontierStep τ/2)∉bulkConstantSet τ := by
  rintro ⟨θ,y,_,hy,hm,he⟩
  have hh := bulk_constant_strict_upper (θ:=θ) hy hτ hm
  rw [←he] at hh
  exact (lt_irrefl _) hh

/-- Source frontier(iv): every smaller-step flow pair is dominated by one arc point. -/
theorem frontier_pair_domination {θ y τ : ℝ} (hθ : 0<θ) (_hy : 0<y) (hτ : 0≤τ)
    (hmargin : y*(1+2*τ)≤4) :
    ∃ θ' : ℝ,2*Real.sqrt (frontierStep τ)≤θ' ∧ θ'≤3*Real.sqrt (frontierStep τ/2) ∧
      Flow.cQ θ y≤Flow.cQ θ' (frontierStep τ) ∧ Flow.cF θ y≤θ'/3 ∧
        Flow.cF θ' (frontierStep τ)=θ'/3 := by
  obtain ⟨θ',hl,hu,hq,hf,he⟩ := Flow.pareto_domination hθ (frontierStep_pos hτ)
  have hY := (margin_le_iff_frontierStep hτ).mp hmargin
  exact ⟨θ',hl,hu,(cQ_mono_step θ hY).trans hq,(cF_mono_step θ hY).trans hf,he⟩

theorem alternating_threshold_iff {θ τ s : ℝ} (hτ : 0<τ) :
    θ/3≤alternatingConstant θ τ s ↔
      2*θ+(4*τ/(1+2*τ))*(θ/3)≤s := by
  have hd : 0<1+2*τ := by linarith
  have he : (4*τ/(1+2*τ))*(θ/3)=(θ/3)*(4*τ)/(1+2*τ) := by ring
  rw [he]
  unfold alternatingConstant
  rw [le_div_iff₀ (by positivity : 0<4*τ)]
  constructor
  · intro hh
    have hi : (θ/3)*(4*τ)/(1+2*τ)≤s-2*θ := (div_le_iff₀ hd).mpr (by nlinarith only [hh])
    linarith
  · intro hh
    have hi : (θ/3)*(4*τ)/(1+2*τ)≤s-2*θ := by linarith
    exact (div_le_iff₀ hd).mp hi

theorem boundary_optimum_iff {τ s : ℝ} (hτ : 0<τ) :
    min (Flow.cF (3*Real.sqrt (frontierStep τ/2)) (frontierStep τ))
      (alternatingConstant (3*Real.sqrt (frontierStep τ/2)) τ s)=Real.sqrt (frontierStep τ/2) ↔
      2*(3*Real.sqrt (frontierStep τ/2))+
        (4*τ/(1+2*τ))*((3*Real.sqrt (frontierStep τ/2))/3)≤s := by
  rw [Flow.cF_at_nonlinear_optimal (frontierStep_pos hτ.le)]
  rw [min_eq_left_iff]
  simpa only [show (3*Real.sqrt (frontierStep τ/2))/3=Real.sqrt (frontierStep τ/2) by ring] using
    alternating_threshold_iff (θ:=3*Real.sqrt (frontierStep τ/2)) (s:=s) hτ

end
end nesterov.TwoStep
