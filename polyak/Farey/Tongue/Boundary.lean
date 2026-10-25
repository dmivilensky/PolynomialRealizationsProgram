import polyak.Farey.Tongue.Explicit
import polyak.Farey.Positions.Basic

/-! Rational tongues bound the actual global divergence boundary. -/
noncomputable section
namespace polyak.Farey
open General Levels Set

theorem kappaNumerator_at_cos (y β ω : ℝ) :
    kappaNumerator y β (Real.cos ω)=
      (y-(1+β)*(1-Real.cos ω))^2+(1-β)^2*(Real.sin ω)^2 := by
  have he := Real.sin_sq_add_cos_sq ω
  unfold kappaNumerator
  nlinarith

theorem rationalTongue_gt_one (p : Global.Threshold.ParameterStrip) (j k : ℕ) :
    (1:EReal)<rationalTongue p j k := by
  let q:=Global.Threshold.tuning p ⟨2,by norm_num⟩
  have hN := kappaNumerator_pos q
    (c:=Real.cos (General.Regions.rationalAngle j k))
    ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  dsimp [rationalTongue,tongueBoundary]
  split_ifs with hd
  · have hdiv := div_pos hN hd
    change 0<kappaNumerator p.val.1 p.val.2 (Real.cos (General.Regions.rationalAngle j k)) /
      tongueDenominator p.val.1 p.val.2 (Real.cos (General.Regions.rationalAngle j k))
        ((Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*Real.sin (General.Regions.rationalAngle j k)) at hdiv
    exact_mod_cast (show (1:ℝ)<1+_ from lt_add_of_pos_right 1 hdiv)
  · exact EReal.coe_lt_top _

theorem kappaBoundary_le_rationalTongue (p : Global.Threshold.ParameterStrip) {j k : ℕ}
    (hj : 1≤j) (hjk : 2*j<k) (hcop : j.Coprime k) :
    (Global.Threshold.kappaBoundary p).val≤rationalTongue p j k := by
  let c:=Real.cos (General.Regions.rationalAngle j k)
  let h:=(Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*Real.sin (General.Regions.rationalAngle j k)
  let D:=tongueDenominator p.val.1 p.val.2 c h
  by_cases hd : 0<D
  · let κ : Global.Threshold.ConditionNumber:=⟨1+kappaNumerator p.val.1 p.val.2 c/D,by
      let q:=Global.Threshold.tuning p ⟨2,by norm_num⟩
      have hN:=kappaNumerator_pos q (c:=c) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
      have hp : 0<kappaNumerator p.val.1 p.val.2 c/D:=div_pos hN hd
      exact lt_add_of_pos_right 1 hp⟩
    have he : rationalTongue p j k=(κ.val:EReal) := by
      exact ite_eq_left hd
    let q:=Global.Threshold.tuning p κ
    have hp : Global.Threshold.parameters q=p := Subtype.ext rfl
    have hangle := (rational_tongue_epigraph q hj hjk).mpr (by rw [hp,he]; exact le_rfl)
    let ω : Frequency:=gridFrequency k j (by omega) (by omega) (by omega)
    have hω : (ω:ℝ)=2*Real.pi*j/k := by simp [ω]
    have hθ : (tuningCurve q) ω≤Real.pi/k := by
      change q.angle (ω:ℝ)≤Real.pi/k
      rw [hω]
      exact hangle
    have hfp:=Lattice.rational_atom_feasible (tuningCurve q) hcop (by omega) ω hω hθ
    rw [he]
    exact (Global.Threshold.kappaBoundary_epigraph p κ).mp hfp
  · have he : rationalTongue p j k=⊤ := ite_eq_right hd
    rw [he]
    exact le_top

end polyak.Farey
