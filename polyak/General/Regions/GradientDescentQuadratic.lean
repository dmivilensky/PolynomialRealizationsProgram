import polyak.General.Regions.GradientDescent
import polyak.General.Regions.DominantQuotients

/-! Article: Corollary D(b), the whole gradient-descent range belongs to the
lag-one quadratic regime Q, not merely to the set where actual rates coincide. -/
namespace polyak.General.Regions
noncomputable section

/-- The exact lag-one infimum equals the quadratic rate for every beta=0 tuning. -/
theorem gradientDescent_rOne_eq (q : Tuning) (hb : q.beta=0) : rOne q=q.rhoQ := by
  have hq := gradientDescent_mem_omegaOne q hb
  have hover : Real.sqrt q.beta<q.rhoQ := by
    rw [hb,Real.sqrt_zero,← q.quadraticRate_eq]
    exact Growth.quadraticRate_pos q.x_pos q.x_lt_y (by norm_num)
      q.beta_nonneg q.beta_lt_one (by simpa using q.y_lt)
  by_cases hab : q.rhoB≤q.rhoA
  · apply (dominant_positive_quadratic_regime_iff q hq hover hab).mpr
    obtain ⟨hr,hroot⟩ := q.dominant_a_root hover hab
    have hx : q.x=1-q.rhoA := by
      dsimp [Tuning.a] at hroot
      rw [hb] at hroot
      have he' : q.rhoA^2-(1+0-q.x)*q.rhoA+0=0 := by exact_mod_cast hroot
      have he : q.rhoA^2-(1-q.x)*q.rhoA=0 := by simpa only [add_zero] using he'
      nlinarith
    have hy : q.y≤1+q.rhoA := by
      have he : q.rhoB=|1-q.y| := by simp only [Tuning.rhoB,hb,add_zero,rootRadius_zero_momentum]
      rw [he] at hab
      linarith [(abs_le.mp hab).1]
    have hK : 0≤Kmu q q.rhoA 1 := by
      have he : Kmu q q.rhoA 1=q.rhoA^3*((1-q.rhoA)^2+q.y*(3*q.rhoA-1)) := by
        dsimp [Kmu]; rw [hb]; ring
      rw [he]
      apply mul_nonneg (pow_nonneg hr.le 3)
      by_cases hthird : (1:ℝ)/3≤q.rhoA
      · exact add_nonneg (sq_nonneg _) (mul_nonneg q.y_pos.le (by linarith))
      · have hh := mul_le_mul_of_nonpos_right hy (show 3*q.rhoA-1≤0 by linarith)
        nlinarith [sq_nonneg q.rhoA]
    have he : Kmu q q.rhoA=quadratic 0 (2*q.rhoA^4*(q.y-1)) (Kmu q q.rhoA 0) := by
      funext c; dsimp [Kmu,quadratic]; rw [hb]; ring
    rw [he]
    exact (concave_quadratic_nonneg_iff (by norm_num)).mpr
      ⟨by simpa only [← he] using dominant_Kmu_endpoint q hab,by simpa only [← he] using hK⟩
  · have hab' : q.rhoA<q.rhoB := lt_of_not_ge hab
    apply (dominant_negative_quadratic_regime_iff q hq hover hab').mpr
    obtain ⟨hr,hroot,_,_⟩ := q.dominant_b_root hover hab'.le
    have hy : q.y=1+q.rhoB := by
      dsimp [Tuning.b] at hroot
      rw [hb] at hroot
      have he' : (-q.rhoB)^2-(1+0-q.y)*(-q.rhoB)+0=0 := by exact_mod_cast hroot
      have he : (-q.rhoB)^2-(1-q.y)*(-q.rhoB)=0 := by simpa only [add_zero] using he'
      nlinarith
    have hx : 1-q.rhoB≤q.x := by
      have he : q.rhoA=|1-q.x| := by simp only [Tuning.rhoA,hb,add_zero,rootRadius_zero_momentum]
      rw [he] at hab'
      linarith [(abs_lt.mp hab').2]
    have hr1 : q.rhoB<1 := (le_max_right _ _).trans_lt q.rhoQ_lt_one
    have he : KL q q.rhoB (-1)=q.rhoB^3*(3*q.rhoB^2+2*q.rhoB-1+q.x*(1-q.rhoB)) := by
      dsimp [KL]; rw [hb]; ring
    rw [he]
    apply mul_nonneg (pow_nonneg hr.le 3)
    have hh := mul_le_mul_of_nonneg_right hx (show 0≤1-q.rhoB by linarith)
    nlinarith [sq_nonneg q.rhoB]

end
end polyak.General.Regions
