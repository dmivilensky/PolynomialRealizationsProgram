import nesterov.Spread.HalfGrid

/-! The uniform Fourier margin at every positive integer lag, including
the two recurrent residue classes of the rational centre. -/
namespace nesterov.Spread
noncomputable section
open Set

def bandMargin (D : KernelData) (K : ℕ) (s : ℝ) : ℝ :=
  min (1/4) (min (centerAngle K^2/6) (D.ck*s^2))

theorem bandMargin_pos (D : KernelData) {K : ℕ} (hK : 3≤K) {s : ℝ} (hs : 0<s) :
    0<bandMargin D K s := by
  unfold bandMargin
  exact lt_min (by norm_num) (lt_min (by positivity [centerAngle_pos hK])
    (mul_pos D.ck_pos (sq_pos_of_pos hs)))

theorem bandMargin_le_quarter (D : KernelData) (K : ℕ) (s : ℝ) :
    bandMargin D K s≤1/4 := min_le_left _ _

theorem bandMargin_le_angle (D : KernelData) (K : ℕ) (s : ℝ) :
    bandMargin D K s≤centerAngle K^2/6 := (min_le_right _ _).trans (min_le_left _ _)

theorem bandMargin_le_width (D : KernelData) (K : ℕ) (s : ℝ) :
    bandMargin D K s≤D.ck*s^2 := (min_le_right _ _).trans (min_le_right _ _)

theorem fourier_margin (D : KernelData) {K n : ℕ} (hK : 3≤K) (hn : 1≤n)
    {s : ℝ} (hs : 0<s) (hs1 : s≤D.s1) :
    bandMargin D K s≤
      Real.cos (centerAngle K/2)*D.hat (s*centerAngle K/2)-
        Real.cos (((n:ℝ)+1/2)*centerAngle K)*D.hat (((n:ℝ)+1/2)*(s*centerAngle K)) := by
  let ω := centerAngle K
  let a := s*ω/2
  let x := ((n:ℝ)+1/2)*(s*ω)
  have hω : 0<ω := centerAngle_pos hK
  have hωu : ω≤2*Real.pi/3 := centerAngle_le hK
  have ha : 0<a := by dsimp [a];positivity
  have hau : a≤D.a0 := by
    have he : a≤Real.pi*D.s1/3 := by
      have hh := mul_le_mul hs1 hωu hω.le (by linarith [D.s1_pos])
      dsimp [a]
      nlinarith
    exact he.trans D.s1_scale_le_a0
  have hs6 : s≤1/6 := hs1.trans D.s1_le_one_sixth
  have hx : 3*a≤x := by
    have hnR : (1:ℝ)≤n := by exact_mod_cast hn
    dsimp [x,a]
    nlinarith [mul_pos hs hω]
  have hhalf := D.hat_half ha hau
  have hgap := D.gap ha hau hx
  have hmin : 0≤min (x^2) 1 := le_min (sq_nonneg _) (by norm_num)
  have hhat := D.hat_mem x
  have hhatle : D.hat x≤D.hat a := by nlinarith [mul_nonneg D.ck_pos.le hmin]
  have hc := half_center_cos_ge hK
  change (1/2:ℝ)≤Real.cos (ω/2) at hc
  have hG : 1/4≤Real.cos (ω/2)*D.hat a := by
    have hh := mul_le_mul hc hhalf (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤Real.cos (ω/2))
    norm_num at hh
    exact hh
  change bandMargin D K s≤Real.cos (ω/2)*D.hat a-
    Real.cos (((n:ℝ)+1/2)*ω)*D.hat x
  by_cases hcos : Real.cos (((n:ℝ)+1/2)*ω)≤0
  · have hh := mul_nonpos_of_nonpos_of_nonneg hcos hhat.1
    exact (bandMargin_le_quarter D K s).trans (by linarith)
  have hcospos : 0<Real.cos (((n:ℝ)+1/2)*ω) := lt_of_not_ge hcos
  let l := n%K
  have hlK : l<K := Nat.mod_lt _ (by omega)
  have hreduce : Real.cos (((n:ℝ)+1/2)*ω)=Real.cos (((l:ℝ)+1/2)*ω) :=
    half_grid_reduce n K (by omega)
  by_cases hend : l=0 ∨ l+1=K
  · have hendcos : Real.cos (((n:ℝ)+1/2)*ω)=Real.cos (ω/2) :=
      hreduce.trans (half_grid_endpoints (by omega) hend)
    have hnK : K-1≤n := by
      rcases hend with hl0|hle
      · by_contra hh
        have hnlt : n<K := by omega
        have hr : l=n := Nat.mod_eq_of_lt hnlt
        omega
      · have hle : l≤n := Nat.mod_le _ _
        omega
    have hangle : Real.pi≤((n:ℝ)+1/2)*ω := by
      have hnR : (K:ℝ)≤2*((n:ℝ)+1/2) := by
        have hh : (K:ℝ)≤2*(n:ℝ)+1 := by exact_mod_cast (show K≤2*n+1 by omega)
        linarith
      have hmul := mul_le_mul_of_nonneg_right hnR hω.le
      have he : (K:ℝ)*ω=2*Real.pi := by dsimp [ω,centerAngle];field_simp
      rw [he] at hmul
      linarith
    have hx2 : 2*s≤x := by
      have hh := mul_le_mul_of_nonneg_right hangle hs.le
      dsimp [x]
      nlinarith [Real.pi_gt_three]
    have hxpos : 0≤x := (by positivity : 0≤2*s).trans hx2
    have hsq := (sq_le_sq₀ (by positivity : 0≤2*s) hxpos).mpr hx2
    have hmin2 : 2*s^2≤min (x^2) 1 := by
      apply le_min
      · nlinarith [sq_nonneg s]
      · nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs6)]
    have hdiff : 2*D.ck*s^2≤D.hat a-D.hat x := by
      have hh := mul_le_mul_of_nonneg_left hmin2 D.ck_pos.le
      nlinarith
    have hprod := mul_le_mul hc hdiff (mul_nonneg (mul_nonneg (by norm_num) D.ck_pos.le) (sq_nonneg s))
      (by linarith : 0≤Real.cos (ω/2))
    rw [hendcos]
    exact (bandMargin_le_width D K s).trans (by nlinarith)
  · have hl : 1≤l := by omega
    have hl2 : l+2≤K := by omega
    have hint := half_grid_interior hK hl hl2
    have hcos3 : 0<Real.cos (3*ω/2) := by rw [hreduce] at hcospos;exact hcospos.trans_le hint
    have hK4 : 4≤K := by
      by_contra hh
      have hk : K=3 := by omega
      subst K
      change 0<Real.cos (3*(2*Real.pi/3)/2) at hcos3
      rw [show 3*(2*Real.pi/3)/2=Real.pi by ring,Real.cos_pi] at hcos3
      linarith
    have hωπ : ω≤Real.pi/2 := by
      have hkR : (4:ℝ)≤K := by exact_mod_cast hK4
      have hdiv := div_le_div_of_nonneg_left (by positivity : 0≤2*Real.pi) (by norm_num : (0:ℝ)<4) hkR
      dsimp [ω,centerAngle]
      linarith
    have hcosle : Real.cos (((n:ℝ)+1/2)*ω)≤Real.cos (3*ω/2) := by rwa [hreduce]
    have hprod := mul_le_mul hcosle hhatle hhat.1 hcos3.le
    have hdiff := cos_half_gap hω.le hωπ
    have hmul := mul_le_mul hdiff hhalf (by norm_num : (0:ℝ)≤1/2)
      (by nlinarith [sq_nonneg ω] : 0≤Real.cos (ω/2)-Real.cos (3*ω/2))
    exact (bandMargin_le_angle D K s).trans (by nlinarith)

end
end nesterov.Spread
