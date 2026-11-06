import nesterov.Spread.KernelData
import polyak.General.Regions.SingleHarmonic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Quantitative separation of the half-integer harmonics of a rational band. -/
namespace nesterov.Spread
noncomputable section
open Set

def centerAngle (K : ℕ) : ℝ := 2*Real.pi/K

theorem centerAngle_pos {K : ℕ} (hK : 3≤K) : 0<centerAngle K := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast (show 0<K by omega))

theorem centerAngle_le {K : ℕ} (hK : 3≤K) : centerAngle K≤2*Real.pi/3 := by
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num)
    (by exact_mod_cast hK)

theorem half_center_cos_ge {K : ℕ} (hK : 3≤K) : 1/2≤Real.cos (centerAngle K/2) := by
  have hω := centerAngle_pos hK
  have hu := centerAngle_le hK
  have hh := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith : 0≤centerAngle K/2)
    (by linarith [Real.pi_pos] : Real.pi/3≤Real.pi) (by linarith : centerAngle K/2≤Real.pi/3)
  simpa only [Real.cos_pi_div_three] using hh

theorem half_grid_reduce (n K : ℕ) (hK : 0<K) :
    Real.cos (((n:ℝ)+1/2)*centerAngle K)=
      Real.cos ((((n%K:ℕ):ℝ)+1/2)*centerAngle K) := by
  have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  have hn : (n:ℝ)=(n%K:ℕ)+(n/K:ℕ)*(K:ℝ) := by
    exact_mod_cast (by simpa only [mul_comm] using (Nat.mod_add_div n K).symm : n=n%K+(n/K)*K)
  have he : ((n:ℝ)+1/2)*centerAngle K=
      (((n%K:ℕ):ℝ)+1/2)*centerAngle K+(n/K:ℕ)*(2*Real.pi) := by
    rw [hn]
    unfold centerAngle
    field_simp
    ring
  rw [he,Real.cos_add_nat_mul_two_pi]

theorem half_grid_endpoints {K l : ℕ} (hK : 0<K) (hl : l=0 ∨ l+1=K) :
    Real.cos (((l:ℝ)+1/2)*centerAngle K)=Real.cos (centerAngle K/2) := by
  rcases hl with rfl|hl
  · congr 1
    ring
  · have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
    have hlR : (l:ℝ)+1=K := by exact_mod_cast hl
    have he : ((l:ℝ)+1/2)*centerAngle K=2*Real.pi-centerAngle K/2 := by
      unfold centerAngle
      field_simp
      nlinarith
    rw [he,Real.cos_two_pi_sub]

theorem half_grid_interior {K l : ℕ} (hK : 3≤K) (hl : 1≤l) (hlK : l+2≤K) :
    Real.cos (((l:ℝ)+1/2)*centerAngle K)≤Real.cos (3*centerAngle K/2) := by
  have hw := centerAngle_pos hK
  have hu := centerAngle_le hK
  have hk : (K:ℝ)≠0 := by exact_mod_cast (show K≠0 by omega)
  have hperiod : (K:ℝ)*centerAngle K=2*Real.pi := by
    unfold centerAngle
    field_simp
  have hlo : 3*centerAngle K/2≤((l:ℝ)+1/2)*centerAngle K := by
    have hlR : (1:ℝ)≤l := by exact_mod_cast hl
    nlinarith
  have hhi : ((l:ℝ)+1/2)*centerAngle K≤2*Real.pi-3*centerAngle K/2 := by
    have hlR : (l:ℝ)+2≤K := by exact_mod_cast hlK
    nlinarith
  by_cases hm : ((l:ℝ)+1/2)*centerAngle K≤Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hm hlo
  · have href0 : 0≤2*Real.pi-((l:ℝ)+1/2)*centerAngle K := by linarith
    have hrefπ : 2*Real.pi-((l:ℝ)+1/2)*centerAngle K≤Real.pi := by linarith
    have hrefl : 3*centerAngle K/2≤2*Real.pi-((l:ℝ)+1/2)*centerAngle K := by linarith
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hrefπ hrefl
    simpa only [Real.cos_two_pi_sub] using hh

theorem cos_half_gap {ω : ℝ} (hω : 0≤ω) (hωπ : ω≤Real.pi/2) :
    ω^2/3≤Real.cos (ω/2)-Real.cos (3*ω/2) := by
  have hs1 := Real.mul_le_sin hω hωπ
  have hs2 := Real.mul_le_sin (by linarith : 0≤ω/2)
    (by linarith : ω/2≤Real.pi/2)
  have hmul := mul_le_mul hs1 hs2 (by positivity : 0≤2/Real.pi*(ω/2))
    (Real.sin_nonneg_of_nonneg_of_le_pi hω (by linarith))
  have hgap : Real.cos (ω/2)-Real.cos (3*ω/2)=2*Real.sin ω*Real.sin (ω/2) := by
    have hh := Real.cos_sub_cos (ω/2) (3*ω/2)
    rw [show (ω/2+3*ω/2)/2=ω by ring,
      show (ω/2-3*ω/2)/2= -(ω/2) by ring,Real.sin_neg] at hh
    linarith
  rw [hgap]
  have hπ : Real.pi^2<12 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hratio : ω^2/3≤2*((2/Real.pi*ω)*(2/Real.pi*(ω/2))) := by
    rw [show 2*((2/Real.pi*ω)*(2/Real.pi*(ω/2)))=4*ω^2/Real.pi^2 by
      field_simp;ring]
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [mul_nonneg (sq_nonneg ω) (sub_nonneg.mpr hπ.le)]
  exact hratio.trans (by linarith)

end
end nesterov.Spread
