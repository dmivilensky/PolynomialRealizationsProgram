import polyak.Global.Kernels.GainSmall

/-! Strict loss away from the zero frequency follows from the actual positive bump. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function
open scoped Topology ENNReal NNReal

theorem psi_cos_integrable (ξ:ℝ) : Integrable (fun x:ℝ=>psi x*Real.cos (ξ*x)) :=
  (psi_smooth.continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    psi_compact.mul_right

theorem psi_gap_density (ξ:ℝ) :
    ∫x,psi x*(1-Real.cos (ξ*x))=1-psiHat ξ := by
  simp_rw [mul_sub,mul_one]
  rw [integral_sub psi_integrable (psi_cos_integrable ξ),integral_psi,
    psiHat_integral_cos,integral_psiMeasure]
  rfl

theorem psi_plus_density (ξ:ℝ) :
    ∫x,psi x*(1+Real.cos (ξ*x))=1+psiHat ξ := by
  simp_rw [mul_add,mul_one]
  rw [integral_add psi_integrable (psi_cos_integrable ξ),integral_psi,
    psiHat_integral_cos,integral_psiMeasure]
  rfl

theorem psiHat_gt_neg_one (ξ:ℝ) : -1<psiHat ξ := by
  have hp : 0<∫x,psi x*(1+Real.cos (ξ*x)) := by
    apply integral_pos_of_integrable_nonneg_nonzero
      (f:=fun x:ℝ=>psi x*(1+Real.cos (ξ*x))) (x:=0)
    · exact psi_smooth.continuous.mul (continuous_const.add
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    · exact psi_integrable.add (psi_cos_integrable ξ) |>.congr (ae_of_all _ fun x=>by dsimp;ring)
    · intro x
      exact mul_nonneg (psi_nonneg x) (by linarith [Real.neg_one_le_cos (ξ*x)])
    · simp only [mul_zero,Real.cos_zero]
      exact (mul_pos (psi_pos (by norm_num)) (by norm_num)).ne'
  rw [psi_plus_density] at hp
  linarith

theorem psiHat_lt_one {ξ:ℝ} (hξ:ξ≠0) : psiHat ξ<1 := by
  let x : ℝ := 1/(16*(|ξ|+1))
  have hxpos : 0<x := by dsimp [x];positivity
  have hxsmall : x<1/4 := by
    dsimp [x]
    apply (div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<4)).mpr
    nlinarith [abs_nonneg ξ]
  have ht : |ξ*x|<1 := by
    rw [abs_mul,abs_of_pos hxpos]
    dsimp [x]
    rw [mul_one_div]
    apply (div_lt_one (by positivity : 0<16*(|ξ|+1))).mpr
    nlinarith [abs_nonneg ξ]
  have hpi : (1:ℝ)<2*Real.pi := by nlinarith [Real.two_le_pi]
  have hc : Real.cos (ξ*x)<1 := by
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro he
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt
      (show -(2*Real.pi)<ξ*x by nlinarith [abs_le.mp ht.le])
      (show ξ*x<2*Real.pi by nlinarith [abs_le.mp ht.le])).mp he
    exact (mul_ne_zero hξ hxpos.ne') hz
  have hp : 0<∫t,psi t*(1-Real.cos (ξ*t)) := by
    apply integral_pos_of_integrable_nonneg_nonzero
      (f:=fun t:ℝ=>psi t*(1-Real.cos (ξ*t))) (x:=x)
    · exact psi_smooth.continuous.mul (continuous_const.sub
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    · exact psi_integrable.sub (psi_cos_integrable ξ) |>.congr (ae_of_all _ fun t=>by dsimp;ring)
    · intro t
      exact mul_nonneg (psi_nonneg t) (sub_nonneg.mpr (Real.cos_le_one _))
    · exact (mul_pos (psi_pos (by rwa [abs_of_pos hxpos])) (sub_pos.mpr hc)).ne'
  rw [psi_gap_density] at hp
  linarith

theorem phiHat_lt_one {ξ:ℝ} (hξ:ξ≠0) : phiHat ξ<1 := by
  have hp := psiHat_lt_one hξ
  have hm := psiHat_gt_neg_one ξ
  unfold phiHat
  nlinarith

end polyak.Global.Kernels
