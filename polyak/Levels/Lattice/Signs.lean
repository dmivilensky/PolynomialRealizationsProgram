import polyak.General.Regions.SingleHarmonic
import Mathlib.Algebra.Order.Floor.Ring

/-! The exact signed-lag strip test. Arbitrary integer lags are reduced
using a real fractional part; no positivity assumption on the lag occurs. -/
noncomputable section
namespace polyak.Levels.Lattice

/-- One phase difference, before choosing lattice coordinates. -/
def lagValue (θ φ : ℝ) : ℝ := Real.cos θ-Real.cos (φ-θ)

theorem lagValue_eq_sines (θ φ : ℝ) :
    lagValue θ φ=2*Real.sin (φ/2)*Real.sin (φ/2-θ) := by
  have h₁:=Real.cos_sub (φ/2) (θ-φ/2)
  have h₂:=Real.cos_add (φ/2) (θ-φ/2)
  have he₁ : φ/2-(θ-φ/2)=φ-θ := by ring
  have he₂ : φ/2+(θ-φ/2)=θ := by ring
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [show φ/2-θ= -(θ-φ/2) by ring,Real.sin_neg]
  unfold lagValue
  linarith

/-- On a fundamental turn, strict violation is exactly the initial arc
of angular length twice the phase, including the endpoint phase pi. -/
theorem lagValue_neg_iff {θ φ : ℝ} (hθ : 0<θ) (hθπ : θ≤Real.pi)
    (hφ : 0≤φ) (hφπ : φ<2*Real.pi) :
    lagValue θ φ<0 ↔ 0<φ ∧ φ<2*θ := by
  by_cases hz : φ=0
  · simp [hz,lagValue]
  have hp : 0<φ := lt_of_le_of_ne hφ (Ne.symm hz)
  have hs : 0<Real.sin (φ/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hlo : -Real.pi<φ/2-θ := by linarith
  have hhi : φ/2-θ<Real.pi := by linarith
  rw [lagValue_eq_sines]
  constructor
  · intro hh
    have hsin : Real.sin (φ/2-θ)<0 := by nlinarith
    have harg : φ/2-θ<0 := by
      by_contra hn
      have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_not_gt hn) hhi.le
      linarith
    exact ⟨hp,by linarith⟩
  · rintro ⟨_,hh⟩
    have hsin:=Real.sin_neg_of_neg_of_neg_pi_lt (by linarith : φ/2-θ<0) hlo
    nlinarith

/-- Opposite signs of the sine factors are equivalent to crossing exactly
one integer in a strip of width at most one. -/
theorem lagValue_neg_iff_integer_strip {θ x : ℝ} (hθ : 0<θ) (hθπ : θ≤Real.pi) :
    lagValue θ (2*Real.pi*x)<0 ↔
      ∃ l : ℤ,0<x-l ∧ x-l<θ/Real.pi := by
  let r:=x-(⌊x⌋:ℤ)
  have hr0 : 0≤r := by exact sub_nonneg.mpr (Int.floor_le x)
  have hr1 : r<1 := by exact Int.fract_lt_one x
  have he : lagValue θ (2*Real.pi*x)=lagValue θ (2*Real.pi*r) := by
    unfold lagValue
    have hh : 2*Real.pi*x-θ=(2*Real.pi*r-θ)+(⌊x⌋:ℤ)*(2*Real.pi) := by
      change 2*Real.pi*x-θ=(2*Real.pi*Int.fract x-θ)+(⌊x⌋:ℤ)*(2*Real.pi)
      nlinarith [Int.fract_add_floor x]
    rw [hh,Real.cos_add_int_mul_two_pi]
  rw [he,lagValue_neg_iff hθ hθπ (mul_nonneg (by positivity) hr0) (by nlinarith [Real.pi_pos])]
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨⌊x⌋,?_,?_⟩
    · change 0<r
      nlinarith [Real.pi_pos]
    · change r<θ/Real.pi
      exact (lt_div_iff₀ Real.pi_pos).mpr (by nlinarith)
  · rintro ⟨l,ha,hb⟩
    have hwidth : θ/Real.pi≤1 := (div_le_one Real.pi_pos).mpr hθπ
    have hl : ⌊x⌋=l := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
    have hr : r=x-l := by simp only [r,hl]
    rw [hr]
    exact ⟨by nlinarith [Real.pi_pos],by nlinarith [(lt_div_iff₀ Real.pi_pos).mp hb]⟩

/-- Literal lattice coordinates of the article. -/
def xi (ω θ : ℝ) : ℝ := ω/(2*θ)
def eta (θ : ℝ) : ℝ := Real.pi/θ

theorem signed_lag_neg_iff {θ ω : ℝ} (hθ : 0<θ) (hθπ : θ≤Real.pi) (n : ℤ) :
    lagValue θ (n*ω)<0 ↔
      ∃ l : ℤ,0<(n:ℝ)*xi ω θ-l*eta θ ∧ (n:ℝ)*xi ω θ-l*eta θ<1 := by
  have he : (n:ℝ)*ω=2*Real.pi*((n:ℝ)*ω/(2*Real.pi)) := by field_simp
  rw [he,lagValue_neg_iff_integer_strip hθ hθπ]
  apply exists_congr
  intro l
  have hid : ((n:ℝ)*ω/(2*Real.pi)-l)*(Real.pi/θ)=
      (n:ℝ)*xi ω θ-l*eta θ := by unfold xi eta; field_simp
  have hd : 0<Real.pi/θ := div_pos Real.pi_pos hθ
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨by rw [←hid]; exact mul_pos ha hd,?_⟩
    rw [←hid]
    have hh:=mul_lt_mul_of_pos_right hb hd
    have hc : θ/Real.pi*(Real.pi/θ)=1 := by field_simp
    rwa [hc] at hh
  · rintro ⟨ha,hb⟩
    rw [←hid] at ha hb
    refine ⟨(mul_pos_iff_of_pos_right hd).mp ha,?_⟩
    have hc : θ/Real.pi*(Real.pi/θ)=1 := by field_simp
    rw [←hc] at hb
    exact (mul_lt_mul_iff_left₀ hd).mp (by simpa only [mul_comm] using hb)

end polyak.Levels.Lattice
