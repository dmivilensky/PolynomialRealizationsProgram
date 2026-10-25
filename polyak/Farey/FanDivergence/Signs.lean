import polyak.Farey.FanDivergence.Formulas

/-! All four strict signs, the closed p=2 endpoint, and the genuine
minimizer constraint. -/
noncomputable section
namespace polyak.Farey
open polyak.Levels Set

theorem fan_sine_product_pos {a θ : ℝ} (ha : 0<a) (haπ : a<Real.pi)
    (hθ : 0<θ) (hθa : θ<a) : 0<2*Real.sin a*Real.sin (a-θ) := by
  have h1 := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have h2 := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hθa) (by linarith : a-θ<Real.pi)
  positivity

theorem fan_sine_product_neg {a θ : ℝ} (ha : 0<a) (haπ : a<Real.pi)
    (hθπ : θ≤Real.pi) (haθ : a<θ) : 2*Real.sin a*Real.sin (a-θ)<0 := by
  have h1 := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have h2 := Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr haθ) (by linarith : -Real.pi<a-θ)
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) h1) h2

theorem fan_sine_product_nonneg {a θ : ℝ} (ha : 0<a) (haπ : a<Real.pi)
    (hθ : 0<θ) (hθa : θ≤a) : 0≤2*Real.sin a*Real.sin (a-θ) := by
  have h1 := (Real.sin_pos_of_pos_of_lt_pi ha haπ).le
  have h2 := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hθa) (by linarith : a-θ≤Real.pi)
  positivity

namespace FanParameters

theorem anchor_lag_one_pos (P : FanParameters) (Θ : Curve) (h : Θ P.anchor<P.halfAnchor) :
    0<Θ.lag 1 P.anchor := by
  rw [P.anchor_lag_one]
  exact fan_sine_product_pos P.halfAnchor_bounds.1
    (by linarith [P.halfAnchor_bounds.2,Real.pi_pos]) (Θ.pos _) h

theorem anchor_lag_one_nonneg (P : FanParameters) (Θ : Curve) (h : Θ P.anchor≤P.halfAnchor) :
    0≤Θ.lag 1 P.anchor := by
  rw [P.anchor_lag_one]
  exact fan_sine_product_nonneg P.halfAnchor_bounds.1
    (by linarith [P.halfAnchor_bounds.2,Real.pi_pos]) (Θ.pos _) h

theorem anchor_lag_parent_neg (P : FanParameters) (Θ : Curve) (h : P.firstAngle<Θ P.anchor) :
    Θ.lag (-P.K) P.anchor<0 := by
  rw [P.anchor_lag_parent]
  exact fan_sine_product_neg P.firstAngle_bounds.1 P.firstAngle_bounds.2 (Θ.le_pi _) h

theorem companion_lag_one_neg (P : FanParameters) (Θ : Curve) (h : P.halfCompanion<Θ P.companion) :
    Θ.lag 1 P.companion<0 := by
  rw [P.companion_lag_one]
  exact fan_sine_product_neg P.halfCompanion_bounds.1 P.halfCompanion_bounds.2 (Θ.le_pi _) h

theorem companion_lag_parent_pos (P : FanParameters) (Θ : Curve) (h : Θ P.companion<P.companionAngle) :
    0<Θ.lag (-P.K) P.companion := by
  rw [P.companion_lag_parent]
  exact fan_sine_product_pos P.companionAngle_bounds.1 P.companionAngle_bounds.2 (Θ.pos _) h

theorem four_strict_signs (P : FanParameters) (Θ : Curve)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor<P.halfAnchor)
    (hcomp : P.halfCompanion<Θ P.companion ∧ Θ P.companion<P.companionAngle) :
    0<Θ.lag 1 P.anchor ∧ Θ.lag (-P.K) P.anchor<0 ∧
      0<Θ.lag (-P.K) P.companion ∧ Θ.lag 1 P.companion<0 :=
  ⟨P.anchor_lag_one_pos Θ hmain.2,P.anchor_lag_parent_neg Θ hmain.1,
    P.companion_lag_parent_pos Θ hcomp.2,P.companion_lag_one_neg Θ hcomp.1⟩

theorem companionAngle_lt_half_of_three_le (P : FanParameters) (hp : 3≤P.p) :
    P.companionAngle<Real.pi/2 := by
  have hK := P.K_ge_two
  have hh := mul_nonneg (sub_nonneg.mpr hp) (show 0≤P.K by linarith)
  have h2 : 2*(P.K+1)<P.k := by dsimp [k];nlinarith
  have h2R : (2:ℝ)*(P.K+1)<P.k := by exact_mod_cast h2
  have hkR : (0:ℝ)<P.k := by exact_mod_cast P.k_pos
  dsimp [companionAngle]
  apply (div_lt_iff₀ hkR).mpr
  nlinarith [Real.pi_pos]

theorem companion_phase_lt_half_of_three_le (P : FanParameters) (Θ : Curve)
    (hp : 3≤P.p) (hcomp : Θ P.companion<P.companionAngle) :
    Θ P.companion<Real.pi/2 := hcomp.trans (P.companionAngle_lt_half_of_three_le hp)

theorem minimizer_nonneg (P : FanParameters) (Θ : Curve)
    (hmain : Θ P.anchor≤P.halfAnchor) (hcomp : Θ P.companion≤Real.pi/2)
    {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    0≤u*Θ.minimizer P.companion+v*Θ.minimizer P.anchor := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show Θ P.companion∈Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [Θ.pos P.companion,Real.pi_pos],hcomp⟩)
  have ha := Real.cos_nonneg_of_mem_Icc
    (show Θ P.anchor∈Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [Θ.pos P.anchor,Real.pi_pos],hmain.trans P.halfAnchor_bounds.2.le⟩)
  exact add_nonneg (mul_nonneg hu hc) (mul_nonneg hv ha)

end FanParameters
end polyak.Farey
