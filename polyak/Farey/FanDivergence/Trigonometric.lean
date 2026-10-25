import polyak.Farey.FanDivergence.Remaining

/-! Exact factorization of Δ₂ into the inequality displayed in the paper. -/
noncomputable section
namespace polyak.Farey
open polyak.Levels

def fanP2Expression (P : FanParameters) (Θ : Curve) : ℝ :=
  2*Real.cos P.firstAngle*Real.cos (Real.pi/(2*(P.k:ℝ)))*
    Real.sin (P.firstAngle-(Θ P.anchor-P.firstAngle))*
    Real.cos ((Θ P.companion-P.firstAngle)+Real.pi/(2*(P.k:ℝ))) -
  Real.sin P.firstAngle*Real.sin (Θ P.companion-P.firstAngle)*
    Real.sin (Θ P.anchor-P.firstAngle)

theorem p2_trig_factor (a θ₁ θ₂ : ℝ) :
    Real.sin (2*a)*Real.sin (2*a-θ₂)*Real.sin (Real.pi/2+a/2)*
        Real.sin (Real.pi/2+a/2-θ₁)-
      Real.sin a*Real.sin (θ₁-a)*Real.sin a*Real.sin (θ₂-a)=
    Real.sin a*(2*Real.cos a*Real.cos (a/2)*Real.sin (a-(θ₂-a))*
      Real.cos ((θ₁-a)+a/2)-Real.sin a*Real.sin (θ₁-a)*Real.sin (θ₂-a)) := by
  have h1 : Real.pi/2+a/2-θ₁=Real.pi/2-((θ₁-a)+a/2) := by ring
  have h2 : 2*a-θ₂=a-(θ₂-a) := by ring
  rw [h1,h2,Real.sin_two_mul,add_comm (Real.pi/2) (a/2),
    Real.sin_add_pi_div_two,Real.sin_pi_div_two_sub]
  ring

namespace FanParameters

theorem p2_halfCompanion (P : FanParameters) (hp : P.p=2) :
    P.halfCompanion=P.firstAngle := by
  simp only [halfCompanion,firstAngle,hp,Int.cast_ofNat]
  ring

theorem half_firstAngle (P : FanParameters) : Real.pi/(2*(P.k:ℝ))=P.firstAngle/2 := by
  unfold firstAngle
  ring

theorem p2_companionAngle (P : FanParameters) (hp : P.p=2) :
    P.companionAngle=Real.pi/2+P.firstAngle/2 := by
  have hk : (P.k:ℝ)=2*(P.K:ℝ)+1 := by simp only [k,hp,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_one]
  have hkR : (P.k:ℝ)≠0 := by exact_mod_cast (ne_of_gt P.k_pos)
  unfold companionAngle firstAngle
  field_simp
  nlinarith [hk]

theorem p2_determinant_factor (P : FanParameters) (hp : P.p=2) (Θ : Curve) :
    fanDeterminant P Θ=Real.sin P.firstAngle*fanP2Expression P Θ := by
  have ha : P.halfAnchor=2*P.firstAngle := by
    rw [P.p2_halfAnchor hp]
    unfold firstAngle
    ring
  rw [fanDeterminant,ha,P.p2_halfCompanion hp,P.p2_companionAngle hp]
  rw [p2_trig_factor]
  unfold fanP2Expression
  rw [P.half_firstAngle]

theorem p2_determinant_iff_displayed (P : FanParameters) (hp : P.p=2) (Θ : Curve) :
    0≤fanDeterminant P Θ ↔ 0≤fanP2Expression P Θ := by
  rw [P.p2_determinant_factor hp]
  exact mul_nonneg_iff_of_pos_left
    (Real.sin_pos_of_pos_of_lt_pi P.firstAngle_bounds.1 P.firstAngle_bounds.2)

end FanParameters
end polyak.Farey
