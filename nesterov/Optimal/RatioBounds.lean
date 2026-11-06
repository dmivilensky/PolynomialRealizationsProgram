import nesterov.Optimal.Minimum

/-! Quantitative bounds for the moving corner ratio, without bounds on its coordinates. -/
namespace nesterov.Optimal
noncomputable section
open Set

def numerator (t p s ξ : ℝ) : ℝ := 4*t+2*(t-p-5)*ξ+(s+p+5-4*t)*ξ^2

theorem numerator_difference (t p s ξ : ℝ) :
    numerator t p s ξ-4*(3-ξ)=
      (t-3)*(4+2*ξ-4*ξ^2)-2*p*ξ+(s+p-7)*ξ^2 := by
  unfold numerator
  ring

theorem coordinate_error_bound {t ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) :
    |(t-3)*(4+2*ξ-4*ξ^2)|≤24*|t-3| := by
  have hs : ξ^2≤4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hξ.2) (show 0≤2+ξ by linarith [hξ.1])]
  have h : |4+2*ξ-4*ξ^2|≤24 := abs_le.mpr ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hξ.2) (show 0≤2+ξ by linarith [hξ.1])],by nlinarith [mul_nonneg (sub_nonneg.mpr hξ.2) (show 0≤2+ξ by linarith [hξ.1])]⟩
  rw [abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (abs_nonneg (t-3))

theorem polynomial_lower {p s δ ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2)
    (hδ : 0<δ) (hδ1 : δ≤1) (hs : 7-δ≤s)
    (hr : (max p 0)^2/(s+5+max p 0)≤min δ (δ^2/24)) :
    -8*δ≤ -2*p*ξ+(s+p-7)*ξ^2 := by
  have hx2 : ξ^2≤4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hξ.2) (show 0≤2+ξ by linarith [hξ.1])]
  by_cases hp : p≤0
  · have hA : 0≤(-p)*ξ*(2-ξ) := mul_nonneg
      (mul_nonneg (by linarith) hξ.1) (sub_nonneg.mpr hξ.2)
    have hB := mul_nonneg (show 0≤s-7+δ by linarith) (sq_nonneg ξ)
    have hC := mul_nonneg hδ.le (show 0≤4-ξ^2 by linarith)
    nlinarith
  · have hpp : 0<p := lt_of_not_ge hp
    rw [max_eq_left hpp.le] at hr
    let D : ℝ := s+5+p
    have hD : 0<D := by dsimp [D];linarith
    have hR : p^2≤δ*D := (div_le_iff₀ hD).mp (hr.trans (min_le_left _ _))
    have hR2 : p^2≤δ^2/24*D := (div_le_iff₀ hD).mp (hr.trans (min_le_right _ _))
    by_cases hDbig : 24≤D
    · have hA := sq_nonneg (D*ξ-2*p)
      have hB := mul_nonneg (mul_nonneg hD.le (show 0≤D-24 by linarith)) (sq_nonneg ξ)
      have hC : 0≤2*D*((-2*p*ξ+(s+p-7)*ξ^2)+2*δ) := by
        dsimp [D] at *
        nlinarith
      have hsmall : -2*δ≤ -2*p*ξ+(s+p-7)*ξ^2 := by
        have := (mul_nonneg_iff_of_pos_left (show 0<2*D by positivity)).mp hC
        linarith
      linarith
    · have hDsmall : D<24 := lt_of_not_ge hDbig
      have hbound : p≤δ := by
        have hm := mul_nonneg (sq_nonneg δ) (show 0≤24-D by linarith)
        nlinarith
      have hA := mul_nonneg (show 0≤δ-p by linarith) hξ.1
      have hB := mul_nonneg (show 0≤s+p-7+δ by linarith) (sq_nonneg ξ)
      have hC := mul_nonneg hδ.le (show 0≤4-ξ^2 by linarith)
      have hDξ := mul_nonneg hδ.le (show 0≤2-ξ by linarith [hξ.2])
      nlinarith

theorem ratio_uniform_lower {t p s δ ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2)
    (hδ : 0<δ) (hδ1 : δ≤1) (ht : |t-3|≤δ) (hs : 7-δ≤s)
    (hr : (max p 0)^2/(s+5+max p 0)≤min δ (δ^2/24)) :
    1-8*δ≤numerator t p s ξ/(4*(3-ξ)) := by
  have hP := polynomial_lower hξ hδ hδ1 hs hr
  have hE := coordinate_error_bound (t:=t) hξ
  have hN : -32*δ≤numerator t p s ξ-4*(3-ξ) := by
    rw [numerator_difference]
    have he : -24*δ≤(t-3)*(4+2*ξ-4*ξ^2) := by
      have h := neg_abs_le ((t-3)*(4+2*ξ-4*ξ^2))
      linarith
    linarith
  apply (le_div_iff₀ (by nlinarith [hξ.2] : 0<4*(3-ξ))).mpr
  have hδξ := mul_nonneg hδ.le (sub_nonneg.mpr hξ.2)
  nlinarith

theorem ratio_defect_bound {t p s L : ℝ} (hs : 4≤s)
    (hL : ∀ ξ∈Icc (0:ℝ) 2,L≤numerator t p s ξ/(4*(3-ξ))) :
    (max p 0)^2/(s+5+max p 0)≤12*|1-L|+24*|t-3| := by
  by_cases hp : p≤0
  · rw [max_eq_right hp]
    simp only [zero_pow (by omega : 2≠0),zero_div]
    positivity
  · have hpp : 0<p := lt_of_not_ge hp
    rw [max_eq_left hpp.le]
    let D : ℝ := s+5+p
    let x : ℝ := p/D
    have hD : 0<D := by dsimp [D];linarith
    have hx0 : 0≤x := (div_pos hpp hD).le
    have hx1 : x≤1 := (div_le_one hD).mpr (by dsimp [D];linarith)
    have hx : x∈Icc (0:ℝ) 2 := ⟨hx0,by linarith⟩
    have he := coordinate_error_bound (t:=t) hx
    have hden : 0<4*(3-x) := by linarith
    have hl := (le_div_iff₀ hden).mp (hL x hx)
    have hpure : -2*p*x+(s+p-7)*x^2=
        -(p^2/D)-12*p^2/D^2 := by
      dsimp [x,D]
      field_simp
      ring
    have hP : -2*p*x+(s+p-7)*x^2≤ -(p^2/D) := by
      rw [hpure]
      have h := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤12) (sq_nonneg p)) (sq_nonneg D)
      linarith
    have hN : p^2/D≤4*(3-x)*(1-L)+24*|t-3| := by
      have heupper := le_abs_self ((t-3)*(4+2*x-4*x^2))
      have hdiff := numerator_difference t p s x
      nlinarith
    have hW : 4*(3-x)*(1-L)≤12*|1-L| := by
      have h1 := mul_le_mul_of_nonneg_left (le_abs_self (1-L)) hden.le
      have h2 := mul_le_mul_of_nonneg_right (show 4*(3-x)≤12 by linarith) (abs_nonneg (1-L))
      exact h1.trans h2
    exact hN.trans (by linarith)

end
end nesterov.Optimal
