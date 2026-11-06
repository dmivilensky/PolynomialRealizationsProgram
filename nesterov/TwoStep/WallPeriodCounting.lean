import nesterov.TwoStep.WallPeriods
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Card

/-! The integer-period cutoff and count in Proposition periods. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def periodCutoff (a ε : ℝ) : ℝ := 2*Real.pi/Real.arccos (1-a*ε)
def largestBandPeriod (a ε : ℝ) : ℕ := Nat.floor (periodCutoff a ε)
def smallestBandPeriod (b : ℝ) : ℕ := Nat.ceil (2*Real.pi/Real.arccos (1-b))
def bandPeriodCount (a b ε : ℝ) : ℕ :=
  (Finset.Icc (smallestBandPeriod b) (largestBandPeriod a ε)).card

private theorem one_sub_cos_half (x : ℝ) : 1-Real.cos x=2*(Real.sin (x/2))^2 := by
  have hc := Real.cos_two_mul (x/2)
  rw [show 2*(x/2)=x by ring] at hc
  nlinarith [Real.sin_sq_add_cos_sq (x/2)]

/-- The inverse-cosine cutoff has the exact square-root scale, without a Taylor assumption. -/
theorem periodCutoff_scaled_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun ε : ℝ=>periodCutoff a ε*Real.sqrt ε) (𝓝[>] (0:ℝ))
      (𝓝 (Real.pi*Real.sqrt (2/a))) := by
  let w : ℝ→ℝ := fun ε=>Real.arccos (1-a*ε)
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hw : Tendsto w (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hz : Tendsto (fun ε : ℝ=>1-a*ε) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      simpa only [mul_zero,sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub (he.const_mul a)
    have ht := (Real.continuous_arccos.tendsto 1).comp
      hz
    simpa only [Function.comp_def,Real.arccos_one] using ht
  have hs : Tendsto (fun ε : ℝ=>Real.sinc (w ε/2)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hw2 : Tendsto (fun ε=>w ε/2) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa only [zero_div] using hw.div_const 2
    simpa only [Function.comp_def,Real.sinc_zero] using
      (Real.continuous_sinc.tendsto 0).comp hw2
  have hratio : Tendsto (fun ε : ℝ=>ε/(w ε)^2) (𝓝[>] (0:ℝ)) (𝓝 (1/(2*a))) := by
    have ht := (hs.pow 2).div_const (2*a)
    simp only [one_pow] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin,
      he.eventually (eventually_lt_nhds (show (0:ℝ)<2/a by positivity))] with ε hε hsmall
    change 0<ε at hε
    have harg : -1≤1-a*ε := by
      have hh := (lt_div_iff₀ ha).mp hsmall
      nlinarith
    have harg1 : 1-a*ε<1 := by nlinarith
    have hwp : 0<w ε := Real.arccos_pos.mpr harg1
    have hc : Real.cos (w ε)=1-a*ε := Real.cos_arccos harg harg1.le
    have hsn : Real.sin (w ε/2)=(w ε/2)*Real.sinc (w ε/2) := by
      rw [Real.sinc_of_ne_zero (ne_of_gt (half_pos hwp))]
      field_simp
    have hh := one_sub_cos_half (w ε)
    rw [hc,hsn] at hh
    field_simp
    nlinarith
  have hsqr := hratio.sqrt
  have hlim : 2*Real.sqrt (1/(2*a))=Real.sqrt (2/a) := by
    have h₁ := Real.sq_sqrt (show 0≤1/(2*a) by positivity)
    have h₂ := Real.sq_sqrt (show 0≤2/a by positivity)
    have heq : 4*(1/(2*a))=2/a := by field_simp;ring
    nlinarith [Real.sqrt_nonneg (1/(2*a)),Real.sqrt_nonneg (2/a)]
  have ht := hsqr.const_mul (2*Real.pi)
  have hv : 2*Real.pi*Real.sqrt (1/(2*a))=Real.pi*Real.sqrt (2/a) := by rw [←hlim];ring
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  rw [Real.sqrt_div hε.le,Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.arccos_nonneg _)]
  dsimp [periodCutoff,w]
  ring

/-- Taking the integer floor preserves the leading maximal-period constant. -/
theorem largestBandPeriod_scaled_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun ε : ℝ=>(largestBandPeriod a ε:ℝ)*Real.sqrt ε) (𝓝[>] (0:ℝ))
      (𝓝 (Real.pi*Real.sqrt (2/a))) := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hlo : Tendsto (fun ε : ℝ=>periodCutoff a ε*Real.sqrt ε-Real.sqrt ε)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.pi*Real.sqrt (2/a))) := by
    simpa only [Real.sqrt_zero,sub_zero] using (periodCutoff_scaled_tendsto ha).sub he.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (periodCutoff_scaled_tendsto ha)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hf := Nat.lt_floor_add_one (periodCutoff a ε)
    have hh := mul_le_mul_of_nonneg_right hf.le (Real.sqrt_nonneg ε)
    dsimp [largestBandPeriod]
    nlinarith
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hp : 0≤periodCutoff a ε := div_nonneg (by positivity) (Real.arccos_nonneg _)
    exact mul_le_mul_of_nonneg_right (Nat.floor_le hp) (Real.sqrt_nonneg ε)

theorem largestBandPeriod_tendsto_atTop {a : ℝ} (ha : 0<a) :
    Tendsto (largestBandPeriod a) (𝓝[>] (0:ℝ)) atTop := by
  have hC : 0<Real.pi*Real.sqrt (2/a) := mul_pos Real.pi_pos (Real.sqrt_pos.mpr (by positivity))
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have heS : Tendsto (fun ε : ℝ=>Real.sqrt ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using he.sqrt
  apply tendsto_atTop.mpr
  intro N
  have hsmall : 0<(Real.pi*Real.sqrt (2/a))/(2*((N:ℝ)+1)) := by positivity
  filter_upwards [(largestBandPeriod_scaled_tendsto ha).eventually (eventually_gt_nhds (half_lt_self hC)),
    heS.eventually (eventually_lt_nhds hsmall)] with ε hbig hε
  by_contra hn
  have hN : (largestBandPeriod a ε:ℝ)≤N := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hn))
  have hh := mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg ε)
  have hε' := (lt_div_iff₀ (show 0<2*((N:ℝ)+1) by positivity)).mp hε
  nlinarith [Real.sqrt_nonneg ε]

/-- The number of admitted integer periods has the same leading constant as the maximum. -/
theorem bandPeriodCount_scaled_tendsto {a : ℝ} (ha : 0<a) (b : ℝ) :
    Tendsto (fun ε : ℝ=>(bandPeriodCount a b ε:ℝ)*Real.sqrt ε) (𝓝[>] (0:ℝ))
      (𝓝 (Real.pi*Real.sqrt (2/a))) := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have ht := (largestBandPeriod_scaled_tendsto ha).add
    (he.sqrt.const_mul (1-(smallestBandPeriod b:ℝ)))
  simp only [Real.sqrt_zero,mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [(largestBandPeriod_tendsto_atTop ha).eventually_ge_atTop (smallestBandPeriod b)]
    with ε hε
  dsimp [bandPeriodCount]
  rw [Nat.card_Icc,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
  ring

theorem smallestBandPeriod_ge_three {b : ℝ} (hb : b∈Ioo (0:ℝ) 2) :
    3≤smallestBandPeriod b := by
  have hw : 0<Real.arccos (1-b) := Real.arccos_pos.mpr (by linarith [hb.1])
  have hwπ : Real.arccos (1-b)<Real.pi := Real.arccos_lt_pi.mpr (by linarith [hb.2])
  have hcut : (2:ℝ)<2*Real.pi/Real.arccos (1-b) := (lt_div_iff₀ hw).mpr (by linarith)
  have hh : 2<Nat.ceil (2*Real.pi/Real.arccos (1-b)) := by
    exact_mod_cast (Nat.lt_ceil.mpr hcut)
  exact hh

/-- The trigonometric band is exactly an interval of integer periods. -/
theorem period_band_iff_integer_interval {a b ε : ℝ} (ha : 0<a) (hε : 0<ε)
    (hb : b∈Ioo (0:ℝ) 2) (hsmall : a*ε<b) (K : ℕ) :
    (3≤K ∧ 1-Real.cos (2*Real.pi/K)∈Icc (a*ε) b) ↔
      K∈Icc (smallestBandPeriod b) (largestBandPeriod a ε) := by
  have hap : 0<a*ε := mul_pos ha hε
  have ha2 : a*ε<2 := hsmall.trans hb.2
  let w₁ : ℝ := Real.arccos (1-a*ε)
  let w₂ : ℝ := Real.arccos (1-b)
  have hw₁ : 0<w₁ := Real.arccos_pos.mpr (by linarith)
  have hw₂ : 0<w₂ := Real.arccos_pos.mpr (by linarith [hb.1])
  have hw₁π : w₁<Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hw₂π : w₂<Real.pi := Real.arccos_lt_pi.mpr (by linarith [hb.2])
  have hcos₁ : Real.cos w₁=1-a*ε := Real.cos_arccos (by linarith) (by linarith)
  have hcos₂ : Real.cos w₂=1-b := Real.cos_arccos (by linarith [hb.2]) (by linarith [hb.1])
  have hcutpos : 0≤periodCutoff a ε := (div_pos (mul_pos (by norm_num) Real.pi_pos) hw₁).le
  constructor
  · rintro ⟨hK,hband⟩
    have hω : 2*Real.pi/K∈Ioo (0:ℝ) Real.pi := by
      simpa [polyak.General.Regions.rationalAngle] using
        polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
    have hKp : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
    have hlo : w₁≤2*Real.pi/K := (Real.strictAntiOn_cos.le_iff_ge
      ⟨hω.1.le,hω.2.le⟩ ⟨hw₁.le,hw₁π.le⟩).mp (by rw [hcos₁];linarith [hband.1])
    have hhi : 2*Real.pi/K≤w₂ := (Real.strictAntiOn_cos.le_iff_ge
      ⟨hw₂.le,hw₂π.le⟩ ⟨hω.1.le,hω.2.le⟩).mp (by rw [hcos₂];linarith [hband.2])
    constructor
    · apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hw₂).mpr
      have hh := (div_le_iff₀ hKp).mp hhi
      nlinarith
    · apply (Nat.le_floor_iff hcutpos).mpr
      apply (le_div_iff₀ hw₁).mpr
      have hh := (le_div_iff₀ hKp).mp hlo
      nlinarith
  · intro hK
    have hK3 := (smallestBandPeriod_ge_three hb).trans hK.1
    have hω : 2*Real.pi/K∈Ioo (0:ℝ) Real.pi := by
      simpa [polyak.General.Regions.rationalAngle] using
        polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
    have hKp : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
    have hcut₁ : (K:ℝ)≤periodCutoff a ε := (Nat.le_floor_iff hcutpos).mp hK.2
    have hcut₂ : 2*Real.pi/w₂≤K := Nat.ceil_le.mp hK.1
    have hlo : w₁≤2*Real.pi/K := by
      apply (le_div_iff₀ hKp).mpr
      have hh := (le_div_iff₀ hw₁).mp hcut₁
      nlinarith
    have hhi : 2*Real.pi/K≤w₂ := by
      apply (div_le_iff₀ hKp).mpr
      have hh := (div_le_iff₀ hw₂).mp hcut₂
      nlinarith
    refine ⟨hK3,?_,?_⟩
    · have hh := Real.strictAntiOn_cos.antitoneOn ⟨hw₁.le,hw₁π.le⟩ ⟨hω.1.le,hω.2.le⟩ hlo
      rw [hcos₁] at hh
      linarith
    · have hh := Real.strictAntiOn_cos.antitoneOn ⟨hω.1.le,hω.2.le⟩ ⟨hw₂.le,hw₂π.le⟩ hhi
      rw [hcos₂] at hh
      linarith

def admittedPeriods (θ y τ δ ε : ℝ) : Set ℕ :=
  {K | 3≤K ∧ 1-Real.cos (2*Real.pi/K)∈
    Icc ((1+δ)*periodLowerScale θ τ ε) ((1-δ)*periodBandEdge τ y)}

/-- The literal largest admitted period and the actual number of admitted
integer periods have the leading constant stated in Proposition periods. -/
theorem resonant_periods_asymptotics {θ y τ δ : ℝ} (hθ : 0<θ) (hy : 0<y)
    (hτ₀ : 0≤τ) (hτ : τ<1/2) (hmargin : y*(1+2*τ)<4) (hδ : δ∈Ioo (0:ℝ) (1/2)) :
    ∃ M : ℝ→ℕ,
      (∀ᶠ ε in 𝓝[>] (0:ℝ),IsGreatest (admittedPeriods θ y τ δ ε) (M ε)) ∧
      Tendsto (fun ε : ℝ=>(M ε:ℝ)*Real.sqrt ε) (𝓝[>] (0:ℝ))
        (𝓝 (Real.pi*Real.sqrt (2*(1-2*τ)/((1+δ)*θ)))) ∧
      Tendsto (fun ε : ℝ=>((admittedPeriods θ y τ δ ε).ncard:ℝ)*Real.sqrt ε) (𝓝[>] (0:ℝ))
        (𝓝 (Real.pi*Real.sqrt (2*(1-2*τ)/((1+δ)*θ)))) := by
  let a : ℝ := (1+δ)*θ/(1-2*τ)
  let b : ℝ := (1-δ)*periodBandEdge τ y
  have hedge := (periodBandEdge_mem hθ hy hτ₀ hτ hmargin).2
  have ha : 0<a := div_pos (mul_pos (by linarith [hδ.1]) hθ) (by linarith)
  have hb : b∈Ioo (0:ℝ) 2 := by
    refine ⟨mul_pos (by linarith [hδ.2]) hedge.1,?_⟩
    dsimp [b]
    nlinarith [hδ.1,hedge.1,hedge.2]
  have hl (ε : ℝ) : (1+δ)*periodLowerScale θ τ ε=a*ε := by dsimp [periodLowerScale,a];ring
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have heq : ∀ᶠ ε in 𝓝[>] (0:ℝ),admittedPeriods θ y τ δ ε=
      Icc (smallestBandPeriod b) (largestBandPeriod a ε) := by
    filter_upwards [self_mem_nhdsWithin,
      he.eventually (eventually_lt_nhds (div_pos hb.1 ha))] with ε hε hs
    change 0<ε at hε
    ext K
    change (3≤K ∧ _∈Icc _ _) ↔ _
    rw [hl]
    exact period_band_iff_integer_interval ha hε hb
      (by have hh := (lt_div_iff₀ ha).mp hs;nlinarith) K
  have hv : Real.pi*Real.sqrt (2/a)=Real.pi*Real.sqrt (2*(1-2*τ)/((1+δ)*θ)) := by
    congr 2
    dsimp [a]
    rw [div_div_eq_mul_div]
  refine ⟨largestBandPeriod a,?_,?_,?_⟩
  · filter_upwards [heq,(largestBandPeriod_tendsto_atTop ha).eventually_ge_atTop
      (smallestBandPeriod b)] with ε hε hmax
    rw [hε]
    exact ⟨⟨hmax,le_rfl⟩,fun _ h=>h.2⟩
  · simpa only [hv] using largestBandPeriod_scaled_tendsto ha
  · have ht := bandPeriodCount_scaled_tendsto ha b
    rw [hv] at ht
    apply ht.congr'
    filter_upwards [heq] with ε hε
    rw [hε,Set.ncard_Icc]
    rfl

/-- Every admitted integer period produces the fixed real three-dimensional
from-rest witness and the strict divergence rate of the article. -/
theorem period_band_periodic_rest {θ y τ δ : ℝ} (hθ : 0<θ) (hy : 0<y)
    (hτ₀ : 0≤τ) (hτ : τ<1/2) (hmargin : y*(1+2*τ)<4) (hδ : δ∈Ioo (0:ℝ) (1/2)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ q : Momentum.Tuning,
      q.beta=1-θ*ε ∧ q.tau=τ ∧ q.stepSize=y ∧ q.Stable (ε^2) 1 ∧
      ∀ K∈admittedPeriods θ y τ δ ε,HasPeriodicRestWitness q (ε^2) 1 K ∧
        1<Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' (ε^2) 1 := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hte : Tendsto (fun ε : ℝ=>θ*ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa only [mul_zero] using he.const_mul θ
  filter_upwards [period_band_signs hθ hy hτ₀ hτ hmargin hδ,self_mem_nhdsWithin,
    he.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hte.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hte.eventually (eventually_lt_nhds (show (0:ℝ)<(4-y*(1+2*τ))/2 by linarith))]
      with ε hsign hε he1 ht1 htm
  change 0<ε at hε
  let q : Momentum.Tuning := {
    beta := 1-θ*ε
    tau := τ
    stepSize := y
    beta_nonneg := by linarith
    beta_lt_one := by nlinarith
    tau_nonneg := hτ₀
    step_pos := hy }
  have hμ : 0<ε^2 := sq_pos_of_pos hε
  have hμL : ε^2<1 := by nlinarith
  have hs : q.Stable (ε^2) 1 := (q.stable_iff hμ hμL).mpr (by dsimp [q];nlinarith)
  refine ⟨q,rfl,rfl,rfl,hs,?_⟩
  intro K hK
  have hneg : Ltau q.beta q.tau (q.stepSize*ε^2) (q.stepSize*1)
      (1-Real.cos (2*Real.pi/K))<0 := by
    simpa only [q,mul_one] using hsign.1 _ hK.2
  exact ⟨negative_Ltau_periodic_rest q (K:=K) hμ hμL hs hK.1 hneg,
    negative_Ltau_restRate q (K:=K) hμ hμL hs hK.1 hneg⟩

end
end nesterov.TwoStep
