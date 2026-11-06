import nesterov.Optimal.Model

/-! Quantitative algebra for a nonvanishing but bounded corner dip. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Set Filter
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

theorem cornerN_defect_expansion (a : A) {ξ : ℝ} (hd : 0<F.cornerDefect a) :
    F.cornerNAt a ξ=12-4*ξ-2*F.cornerDefect a*ξ+
      (F.stabilityMargin a+5+F.cornerDefect a-12)*ξ^2+
        (F.thetaAt a-3)*(4+2*ξ-4*ξ^2) := by
  have hpos : 0<4*F.cornerAlpha a-5 := by
    have hh : 0<max (4*F.cornerAlpha a-5) 0 := hd
    exact (lt_max_iff.mp hh).resolve_right (lt_irrefl 0)
  unfold cornerDefect cornerNAt
  rw [max_eq_left hpos.le]
  ring

private theorem shape_bound {ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) :
    |4+2*ξ-4*ξ^2|≤24 := by
  have hsq : ξ^2≤4 := by nlinarith [hξ.1,hξ.2]
  exact abs_le.mpr ⟨by nlinarith,by nlinarith [sq_nonneg ξ]⟩

theorem corner_moderate_dip_bound (a : A) {q ξ : ℝ}
    (hq : 0<q) (hq1 : q≤1) (hd : 0<F.cornerDefect a)
    (hD : q*(F.stabilityMargin a+5+F.cornerDefect a)≤F.cornerDefect a^2)
    (hθ : |F.thetaAt a-3|≤q/192)
    (hξ : ξ∈Icc (0:ℝ) 2)
    (hlo : q/2≤F.cornerDefect a*ξ) (hhi : F.cornerDefect a*ξ≤q) :
    F.cornerNAt a ξ-4*(1-q/48)*(3-ξ)≤ -q/8 := by
  have hshape := shape_bound hξ
  have herr : |(F.thetaAt a-3)*(4+2*ξ-4*ξ^2)|≤q/8 := by
    rw [abs_mul]
    calc
      _≤(q/192)*24 := mul_le_mul hθ hshape (abs_nonneg _) (by positivity)
      _=q/8 := by ring
  have hξsq := sq_nonneg ξ
  have hmul := mul_le_mul_of_nonneg_right hD hξsq
  have hφ : (F.cornerDefect a*ξ)^2≤q*(F.cornerDefect a*ξ) := by
    nlinarith [mul_nonneg (by nlinarith : 0≤F.cornerDefect a*ξ)
      (sub_nonneg.mpr hhi)]
  have hDξ : (F.stabilityMargin a+5+F.cornerDefect a)*ξ^2≤F.cornerDefect a*ξ := by
    apply (mul_le_mul_iff_right₀ hq).mp
    nlinarith only [hmul,hφ]
  rw [F.cornerN_defect_expansion a hd]
  have hnon := mul_nonneg (show 0≤1-q/48 by linarith) hξ.1
  nlinarith [(abs_le.mp herr).2]

theorem corner_moderate_N_bound (a : A) {q ξ : ℝ}
    (hq : 0<q) (hq1 : q≤1) (hd : 0<F.cornerDefect a)
    (hD0 : 0≤F.stabilityMargin a+5+F.cornerDefect a)
    (hD : q*(F.stabilityMargin a+5+F.cornerDefect a)≤F.cornerDefect a^2)
    (hθ : |F.thetaAt a-3|≤q/192)
    (hξ : ξ∈Icc (0:ℝ) 2)
    (hlo : q/2≤F.cornerDefect a*ξ) (hhi : F.cornerDefect a*ξ≤q) :
    |F.cornerNAt a ξ|≤100 := by
  have hshape := shape_bound hξ
  have herr : |(F.thetaAt a-3)*(4+2*ξ-4*ξ^2)|≤q/8 := by
    rw [abs_mul]
    calc
      _≤(q/192)*24 := mul_le_mul hθ hshape (abs_nonneg _) (by positivity)
      _=q/8 := by ring
  have hsq : ξ^2≤4 := by nlinarith [hξ.1,hξ.2]
  have hmul := mul_le_mul_of_nonneg_right hD (sq_nonneg ξ)
  have hφ : (F.cornerDefect a*ξ)^2≤q*(F.cornerDefect a*ξ) := by
    nlinarith [mul_nonneg (by nlinarith : 0≤F.cornerDefect a*ξ)
      (sub_nonneg.mpr hhi)]
  have hDξ : (F.stabilityMargin a+5+F.cornerDefect a)*ξ^2≤F.cornerDefect a*ξ := by
    apply (mul_le_mul_iff_right₀ hq).mp
    nlinarith only [hmul,hφ]
  have hDξ0 := mul_nonneg hD0 (sq_nonneg ξ)
  rw [F.cornerN_defect_expansion a hd]
  exact abs_le.mpr ⟨by nlinarith [(abs_le.mp herr).1],by nlinarith [(abs_le.mp herr).2]⟩

end
end nesterov.TwoStep.Scaling
