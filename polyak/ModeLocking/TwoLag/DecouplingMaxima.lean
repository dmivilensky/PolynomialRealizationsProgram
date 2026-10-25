import polyak.ModeLocking.TwoLag.Signs
import polyak.Levels.Geometry.LagOne

/-! Attainment of the independent positive-side ratio follows from the
closed dip; it is not an additional hypothesis in Proposition decouple. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Levels Set

def plusSet (Θ : Curve) (K : ℕ) : Set Frequency :=
  {ω | 0<Θ.lag 1 ω ∧ Θ.lag (-(K : ℤ)) ω<0}
def minusSet (Θ : Curve) (K : ℕ) : Set Frequency :=
  {ω | 0<Θ.lag (-(K : ℤ)) ω ∧ Θ.lag 1 ω<0}
def plusRatio (Θ : Curve) (K : ℕ) (ω : Frequency) : ℝ :=
  Θ.lag 1 ω/(-Θ.lag (-(K : ℤ)) ω)
def minusRatio (Θ : Curve) (K : ℕ) (ω : Frequency) : ℝ :=
  Θ.lag (-(K : ℤ)) ω/(-Θ.lag 1 ω)

def NoCommonNonnegative (Θ : Curve) (K : ℕ) : Prop :=
  ∀ω : Frequency,0<(ω : ℝ)→¬(0≤Θ.lag 1 ω ∧ 0≤Θ.lag (-(K : ℤ)) ω)

theorem closedDip_lag_one_nonneg (Θ : Curve) {ω : Frequency} (hω : ω∈Geometry.closedDip Θ) :
    0≤Θ.lag 1 ω := by
  by_cases hd : ω∈Geometry.dip Θ
  · exact ((Geometry.lag_one_pos_iff Θ ω).mpr hd).le
  · exact (Geometry.lag_one_zero_on_closedDip_boundary Θ hω hd).ge

theorem plusSet_subset_closedDip (Θ : Curve) (K : ℕ) : plusSet Θ K⊆Geometry.closedDip Θ := by
  intro ω hω
  exact (show Θ ω<(ω : ℝ)/2 from (Geometry.lag_one_pos_iff Θ ω).mp hω.1).le

theorem minus_lag_neg_on_closedDip {Θ : Curve} {K : ℕ} (hno : NoCommonNonnegative Θ K)
    {ω : Frequency} (hω : ω∈Geometry.closedDip Θ) : Θ.lag (-(K : ℤ)) ω<0 := by
  have hx := Geometry.closedDip_interior_frequency Θ hω
  exact lt_of_not_ge (fun h=>hno ω hx.1 ⟨closedDip_lag_one_nonneg Θ hω,h⟩)

theorem plusRatio_pos {Θ : Curve} {K : ℕ} {ω : Frequency} (hω : ω∈plusSet Θ K) :
    0<plusRatio Θ K ω := div_pos hω.1 (neg_pos.mpr hω.2)

theorem minusRatio_pos {Θ : Curve} {K : ℕ} {ω : Frequency} (hω : ω∈minusSet Θ K) :
    0<minusRatio Θ K ω := div_pos hω.1 (neg_pos.mpr hω.2)

theorem plus_minimizer_pos {Θ : Curve} {K : ℕ} {ω : Frequency} (hω : ω∈plusSet Θ K) :
    0<Θ.minimizer ω := by
  have hd : Θ ω<(ω : ℝ)/2 := (Geometry.lag_one_pos_iff Θ ω).mp hω.1
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Θ.pos ω,Real.pi_pos],by linarith [ω.property.2]⟩

/-- The positive-side supremum is attained whenever its domain is nonempty. -/
theorem plusRatio_attained {Θ : Curve} {K : ℕ} (hno : NoCommonNonnegative Θ K)
    (hne : (plusSet Θ K).Nonempty) :
    ∃u∈plusSet Θ K,∀ω∈plusSet Θ K,plusRatio Θ K ω≤plusRatio Θ K u := by
  have hc : ContinuousOn (plusRatio Θ K) (Geometry.closedDip Θ) :=
    (Θ.continuous_lag 1).continuousOn.div (Θ.continuous_lag (-(K : ℤ))).neg.continuousOn
      (fun ω hω=>neg_ne_zero.mpr (minus_lag_neg_on_closedDip hno hω).ne)
  obtain ⟨v,hv⟩ := hne
  obtain ⟨u,hu,hmax⟩ := (Geometry.closedDip_isCompact Θ).exists_isMaxOn
    ⟨v,plusSet_subset_closedDip Θ K hv⟩ hc
  have hpos : 0<plusRatio Θ K u :=
    (plusRatio_pos hv).trans_le (hmax (plusSet_subset_closedDip Θ K hv))
  have hneg := minus_lag_neg_on_closedDip hno hu
  have hlag : 0<Θ.lag 1 u := by
    have h := (div_pos_iff_of_pos_right (neg_pos.mpr hneg)).mp hpos
    exact h
  exact ⟨u,⟨hlag,hneg⟩,fun ω hω=>hmax (plusSet_subset_closedDip Θ K hω)⟩

end polyak.ModeLocking.TwoLag
