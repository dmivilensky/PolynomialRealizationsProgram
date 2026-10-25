import polyak.Farey.FanDivergence.Signs

/-! The displayed fan determinant and the complete admissible ratio
interval for the two actual lag constraints. -/
noncomputable section
namespace polyak.Farey
open polyak.Levels

def fanDeterminant (P : FanParameters) (Θ : Curve) : ℝ :=
  Real.sin P.halfAnchor * Real.sin (P.halfAnchor-Θ P.anchor) *
    Real.sin P.companionAngle * Real.sin (P.companionAngle-Θ P.companion) -
  Real.sin P.halfCompanion * Real.sin (Θ P.companion-P.halfCompanion) *
    Real.sin P.firstAngle * Real.sin (Θ P.anchor-P.firstAngle)

def FanPairFeasible (P : FanParameters) (Θ : Curve) : Prop :=
  TwoLagFeasible (Θ.lag 1 P.anchor) (-Θ.lag (-P.K) P.anchor)
    (-Θ.lag 1 P.companion) (Θ.lag (-P.K) P.companion)

def FanRatioAdmissible (P : FanParameters) (Θ : Curve) (r : ℝ) : Prop :=
  (-Θ.lag (-P.K) P.anchor)/Θ.lag (-P.K) P.companion≤r ∧
    r≤Θ.lag 1 P.anchor/(-Θ.lag 1 P.companion)

theorem fanPairFeasible_iff_weights (P : FanParameters) (Θ : Curve) :
    FanPairFeasible P Θ ↔ ∃u v : ℝ,0≤u ∧ 0≤v ∧ 0<u+v ∧
      0≤u*Θ.lag 1 P.companion+v*Θ.lag 1 P.anchor ∧
      0≤u*Θ.lag (-P.K) P.companion+v*Θ.lag (-P.K) P.anchor := by
  unfold FanPairFeasible TwoLagFeasible
  constructor <;> rintro ⟨u,v,hu,hv,hne,h1,h2⟩ <;>
    exact ⟨u,v,hu,hv,hne,by nlinarith,by nlinarith⟩

theorem fan_determinant_identity (P : FanParameters) (Θ : Curve) :
    Θ.lag 1 P.anchor*Θ.lag (-P.K) P.companion-
      Θ.lag (-P.K) P.anchor*Θ.lag 1 P.companion=4*fanDeterminant P Θ := by
  rw [P.anchor_lag_one,P.companion_lag_parent,P.anchor_lag_parent,P.companion_lag_one]
  have h1 : P.firstAngle-Θ P.anchor= -(Θ P.anchor-P.firstAngle) := by ring
  have h2 : P.halfCompanion-Θ P.companion= -(Θ P.companion-P.halfCompanion) := by ring
  rw [h1,h2,Real.sin_neg,Real.sin_neg]
  unfold fanDeterminant
  ring

theorem fan_pair_determinant_iff (P : FanParameters) (Θ : Curve)
    (hmain : P.firstAngle<Θ P.anchor)
    (hcomp : P.halfCompanion<Θ P.companion ∧ Θ P.companion<P.companionAngle) :
    FanPairFeasible P Θ ↔ 0≤fanDeterminant P Θ := by
  unfold FanPairFeasible
  rw [twoLag_feasible_iff (neg_pos.mpr (P.anchor_lag_parent_neg Θ hmain))
    (neg_pos.mpr (P.companion_lag_one_neg Θ hcomp.1)) (P.companion_lag_parent_pos Θ hcomp.2)]
  have he := fan_determinant_identity P Θ
  rw [neg_mul_neg]
  constructor <;> intro h <;> nlinarith

theorem fan_pair_positive_weights (P : FanParameters) (Θ : Curve)
    (hmain : P.firstAngle<Θ P.anchor) (hcomp : P.halfCompanion<Θ P.companion)
    {u v : ℝ} (hu : 0≤u) (hv : 0≤v) (hne : 0<u+v)
    (h1 : 0≤u*Θ.lag 1 P.companion+v*Θ.lag 1 P.anchor)
    (h2 : 0≤u*Θ.lag (-P.K) P.companion+v*Θ.lag (-P.K) P.anchor) :
    0<u ∧ 0<v := by
  apply twoLag_weights_pos (A:=Θ.lag 1 P.anchor) (D:=Θ.lag (-P.K) P.companion)
    (neg_pos.mpr (P.anchor_lag_parent_neg Θ hmain))
    (neg_pos.mpr (P.companion_lag_one_neg Θ hcomp)) hu hv hne
  · nlinarith
  · nlinarith

theorem fan_ratio_constraints_iff (P : FanParameters) (Θ : Curve)
    (hcomp : P.halfCompanion<Θ P.companion ∧ Θ P.companion<P.companionAngle) (r : ℝ) :
    (0≤r*Θ.lag 1 P.companion+Θ.lag 1 P.anchor ∧
      0≤r*Θ.lag (-P.K) P.companion+Θ.lag (-P.K) P.anchor) ↔ FanRatioAdmissible P Θ r := by
  have he := twoLag_ratio_iff (A:=Θ.lag 1 P.anchor) (B:= -Θ.lag (-P.K) P.anchor)
    (r:=r) (neg_pos.mpr (P.companion_lag_one_neg Θ hcomp.1))
    (P.companion_lag_parent_pos Θ hcomp.2)
  unfold FanRatioAdmissible
  constructor
  · rintro ⟨h1,h2⟩
    exact he.mp ⟨by nlinarith,by nlinarith⟩
  · intro h
    obtain ⟨h1,h2⟩ := he.mpr h
    exact ⟨by nlinarith,by nlinarith⟩

theorem fan_admissible_ratio_pos (P : FanParameters) (Θ : Curve)
    (hmain : P.firstAngle<Θ P.anchor) (hcomp : Θ P.companion<P.companionAngle)
    {r : ℝ} (hr : FanRatioAdmissible P Θ r) : 0<r :=
  (div_pos (neg_pos.mpr (P.anchor_lag_parent_neg Θ hmain))
    (P.companion_lag_parent_pos Θ hcomp)).trans_le hr.1

end polyak.Farey
