import polyak.Boundary.P2.Bounds

/-!
Article: Theorem p2arc(i),(vii) and Lemma p2ends.
Use: exact monotonic parametrization, the two physical switch values and source derivatives.
-/

namespace polyak.Boundary.P2
noncomputable section
open Spectral

/-- Article: the rational parameter is positive throughout J. -/
theorem parameter_pos {z : ℝ} (hz : z∈parameterInterval) : 0<z := by
  have h := hz.1
  norm_num [parameterInterval] at h
  linarith

/-- Article: all r₋ denominators are strictly positive on J. -/
theorem rMinus_pos {z : ℝ} (hz : z∈parameterInterval) : 0<rMinus z := by
  have hl : (3/2 : ℝ) ≤ z := by have h:=hz.1; norm_num [parameterInterval] at h; linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3/2) hl 2
  unfold rMinus
  nlinarith

/-- Article: the negative e₋ factor used by G′. -/
theorem eMinus_neg {z : ℝ} (hz : z∈parameterInterval) : eMinus z<0 := by
  have hl : (3/2 : ℝ) ≤ z := by have h:=hz.1; norm_num [parameterInterval] at h; linarith
  have hu : z ≤ (7/4 : ℝ) := by have h:=hz.2; norm_num [parameterInterval] at h; linarith
  have hs := pow_le_pow_left₀ (parameter_pos hz).le hu 2
  unfold eMinus
  nlinarith

/-- Article: the positive e₊ factor used by G′. -/
theorem ePlus_pos {z : ℝ} (hz : z∈parameterInterval) : 0<ePlus z := by
  have hl : (3/2 : ℝ) ≤ z := by have h:=hz.1; norm_num [parameterInterval] at h; linarith
  unfold ePlus
  nlinarith [sq_nonneg z]

/-- Article: exact rational derivative dG/dζ. -/
def GDerivative (z : ℝ) : ℝ := rPlus z*eMinus z*ePlus z/(8*z^2*rMinus z^2)

/-- Article: actual differentiability of the physical parameter map. -/
theorem hasDerivAt_G {z : ℝ} (hz : z∈parameterInterval) : HasDerivAt G (GDerivative z) z := by
  have h0 := (parameter_pos hz).ne'
  have hr := (rMinus_pos hz).ne'
  have hd := (((hasDerivAt_id z).pow 4).add_const 4).div
    (((hasDerivAt_id z).const_mul 8).mul (((hasDerivAt_id z).pow 2).sub_const 2))
      (show 8*z*(z^2-2)≠0 by exact mul_ne_zero (mul_ne_zero (by norm_num) h0) hr)
  convert hd using 1
  · rfl
  · dsimp [GDerivative,rPlus,eMinus,ePlus,rMinus]
    norm_num
    field_simp
    ring

/-- Article: G′ is strictly negative on the whole source interval. -/
theorem GDerivative_neg {z : ℝ} (hz : z∈parameterInterval) : GDerivative z<0 := by
  unfold GDerivative
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (rPlus_pos z) (eMinus_neg hz)) (ePlus_pos hz))
    (by have hp:=parameter_pos hz; have hr:=rMinus_pos hz; positivity)

/-- Article: G decreases strictly throughout the full verified parameter interval. -/
theorem G_strictAntiOn : StrictAntiOn G parameterInterval := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun z hz => (hasDerivAt_G hz).continuousAt.continuousWithinAt
  · intro z hz
    have hm : z∈parameterInterval := interior_subset hz
    rw [(hasDerivAt_G hm).deriv]
    exact GDerivative_neg hm

/-- Article: direct quotient-rule derivative of u, prior to its source factorization. -/
def uDerivative (z : ℝ) : ℝ :=
  ((2*qMinus z*(2*z-2))*(z^4-4)-qMinus z^2*(4*z^3))/(z^4-4)^2

/-- Article: the rational twist is actually differentiable. -/
theorem hasDerivAt_u_direct {z : ℝ} (hz : z∈parameterInterval) : HasDerivAt u (uDerivative z) z := by
  have hr := (rMinus_pos hz).ne'
  have hp := (rPlus_pos z).ne'
  have h4 : z^4-4≠0 := by
    have he : z^4-4=rMinus z*rPlus z := by unfold rMinus rPlus; ring
    rw [he]
    exact mul_ne_zero hr hp
  have hd := (((((hasDerivAt_id z).pow 2).sub ((hasDerivAt_id z).const_mul 2)).add_const 2).pow 2).div
    (((hasDerivAt_id z).pow 4).sub_const 4) h4
  convert hd using 1
  · rfl
  · dsimp [uDerivative,qMinus]
    norm_num

/-- Article: exact rational identity du/dζ=(du/dG)(dG/dζ). -/
theorem uDerivative_eq {z : ℝ} (hz : z∈parameterInterval) : uDerivative z=slope z*GDerivative z := by
  have h0 := (parameter_pos hz).ne'
  have hr := (rMinus_pos hz).ne'
  have hp := (rPlus_pos z).ne'
  have hem := (eMinus_neg hz).ne
  have hep := (ePlus_pos hz).ne'
  have h4 : z^4-4=rMinus z*rPlus z := by unfold rMinus rPlus; ring
  unfold uDerivative slope GDerivative
  rw [h4]
  field_simp
  dsimp only [qMinus,rMinus,rPlus,eMinus,ePlus]
  ring

/-- Article: the actual derivative du/dG is the certified rational slope. -/
theorem hasDerivAt_u {z : ℝ} (hz : z∈parameterInterval) :
    HasDerivAt u (slope z*GDerivative z) z := by
  rw [←uDerivative_eq hz]
  exact hasDerivAt_u_direct hz

/-- Article: the slope satisfies the exact strict bounds 0<du/dG<1. -/
theorem slope_bounds {z : ℝ} (hz : z∈parameterInterval) : 0<slope z ∧ slope z<1 := by
  exact ⟨slope_positive_positive z hz,by have h:=slope_lt_one_positive z hz; linarith⟩

/-- Article: the physical lower endpoint Gₐ. -/
def Ga : ℝ := G zetaA

/-- Article: the physical spiral endpoint equals the independently isolated cubic root G₁. -/
theorem G_zeta1 : G zeta1=Boundary.G1 := by
  apply Boundary.spiralSwitch_strictMonoOn.injOn
    (show 1 ≤ G zeta1 from (one_lt_G zeta1_mem).le)
    (show 1 ≤ Boundary.G1 by linarith [Boundary.G1_bounds.1])
  exact (switchComposition_modular zeta1_mem endpointCubic_zeta1).trans Boundary.spiralSwitch_G1.symm

/-- Article: the physical endpoints are ordered. -/
theorem Ga_lt_G1 : Ga<Boundary.G1 := by
  have h := G_strictAntiOn zeta1_mem zetaA_mem zeta1_lt_zetaA
  rw [G_zeta1] at h
  exact h

/-- Article: the endpoint Gₐ satisfies exactly the printed degree-twelve source equation. -/
theorem Ha_Ga : Ha Ga=0 := haComposition_modular zetaA_mem N12_zetaA

/-- Article: source parameter enclosure for the full closed arc. -/
private theorem parameter_arc_mem {z : ℝ} (hz : z∈Set.Icc zeta1 zetaA) : z∈parameterInterval := by
  constructor <;> linarith [hz.1,hz.2,zeta1_bounds.1,zetaA_bounds.2]

/-- Article: each physical G on the closed P₂ arc has one and only one rational parameter. -/
theorem existsUnique_parameter {G₀ : ℝ} (hG : G₀∈Set.Icc Ga Boundary.G1) :
    ∃! z : ℝ,z∈Set.Icc zeta1 zetaA ∧ G z=G₀ := by
  have hc : ContinuousOn (fun z => -G z) (Set.Icc zeta1 zetaA) := by
    intro z hz
    exact (hasDerivAt_G (parameter_arc_mem hz)).continuousAt.neg.continuousWithinAt
  have htarget : -G₀∈Set.Icc (-G zeta1) (-G zetaA) := by
    rw [G_zeta1]
    change -Boundary.G1 ≤ -G₀ ∧ -G₀ ≤ -Ga
    constructor <;> linarith [hG.1,hG.2]
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc zeta1_lt_zetaA.le hc htarget
  refine ⟨z,⟨hz,by linarith⟩,fun z' hz' => ?_⟩
  exact G_strictAntiOn.injOn (parameter_arc_mem hz'.1) (parameter_arc_mem hz) (by linarith [hz'.2,he])

end
end polyak.Boundary.P2
