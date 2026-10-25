import polyak.FareyPlateau.Edge.Jets
import polyak.FareyPlateau.LargeCurvature.ThreeLag

/-! Zone B of largea: each lag is strictly negative throughout the part
of the central interval above phase pi/2. The claim is for the entire interval. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open Levels
open scoped BigOperators

theorem lag_middle_zone {n : ℤ} {ω₀ δ c θ : ℝ}
    (hphase : ∃ z : ℤ, (n:ℝ)*ω₀=2*c+(z:ℝ)*(2*Real.pi))
    (he : 0<c+(n:ℝ)*δ/2 ∧ c+(n:ℝ)*δ/2<Real.pi/2)
    (hθ : Real.pi/2<θ) (hθπ : θ≤Real.pi) :
    Geometry.extendedLag (fun _=>θ) n (ω₀+δ)<0 := by
  obtain ⟨z,hz⟩ := hphase
  have heπ : c+(n:ℝ)*δ/2<Real.pi := by linarith [he.2,Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi he.1 heπ
  have hminus : -Real.pi<c+(n:ℝ)*δ/2-θ := by linarith [he.1]
  have hnegative : c+(n:ℝ)*δ/2-θ<0 := by linarith [he.2]
  have hn := Real.sin_neg_of_neg_of_neg_pi_lt hnegative hminus
  unfold Geometry.extendedLag
  have hid : (n:ℝ)*(ω₀+δ)-θ = (2*(c+(n:ℝ)*δ/2)-θ)+(z:ℝ)*(2*Real.pi) := by
    linear_combination hz
  rw [hid,Real.cos_add_int_mul_two_pi]
  have hprod : Real.cos θ-Real.cos (2*(c+(n:ℝ)*δ/2)-θ)=
      2*Real.sin (c+(n:ℝ)*δ/2)*Real.sin (c+(n:ℝ)*δ/2-θ) := by
    rw [Real.cos_sub_cos]
    rw [show (θ+(2*(c+(n:ℝ)*δ/2)-θ))/2=c+(n:ℝ)*δ/2 by ring,
      show (θ-(2*(c+(n:ℝ)*δ/2)-θ))/2= -(c+(n:ℝ)*δ/2-θ) by ring,
      Real.sin_neg]
    ring
  rw [hprod]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hs) hn

theorem middle_zone_angles {k N n δ : ℝ} (hk : 5≤k) (hN : 0<N)
    (hn : |n|≤N) (hδ : |δ|≤Real.pi/(k*N)) :
    0<Real.pi/k+n*δ/2 ∧ Real.pi/k+n*δ/2<Real.pi/2 := by
  have hkpos : 0<k := by linarith
  have hprod : |n*δ|≤Real.pi/k := by
    rw [abs_mul]
    have hp := mul_le_mul hn hδ (abs_nonneg _) hN.le
    have he : N*(Real.pi/(k*N))=Real.pi/k := by field_simp
    rwa [he] at hp
  obtain ⟨hl,hu⟩ := abs_le.mp hprod
  have hc : 0<Real.pi/k := by positivity
  have hcupper : 3*(Real.pi/k)/2 < Real.pi/2 := by
    apply (div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr
    have hh : 3*(Real.pi/k)<Real.pi := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hkpos).mpr
      nlinarith [Real.pi_pos]
    exact hh
  constructor <;> linarith

end polyak.FareyPlateau.LargeCurvature
