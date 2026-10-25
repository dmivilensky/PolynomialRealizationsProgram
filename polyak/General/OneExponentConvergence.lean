import polyak.General.OneExponent
import polyak.Threshold.Convergence

/-! The source consequence after Theorem one exponent: infeasibility at
zero proves convergence of every actual trajectory in the original class.
The stronger free growth estimate also covers arbitrary Hilbert spaces. -/
noncomputable section
namespace polyak.General
open Dynamics Growth Duality Spectral Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem converges_of_certificate {μ L α β t : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (hα : 0<α) (hβ : 0≤β) (ht : t≤0)
    (hr : rootRadius (normalizedA μ L α β) β<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap (normalizedA μ L α β)
      (normalizedB μ L α) β t) t) (a : E) (hmin : ∀ y,f a≤f y) (x₀ : E) :
    Tendsto (iterate (gradient f) α β x₀) atTop (𝓝 a) := by
  have hBp : 0<normalizedB μ L α:=
    div_pos (mul_pos hα (sub_pos.mpr hf.mu_lt_L)) (by norm_num)
  have hB:=ne_of_gt hBp
  let r:=growthRate (normalizedA μ L α β) (normalizedB μ L α) β
  let R:=(r+1)/2
  have hrp : 0<r:=growthRate_pos _ _ _
  have hr1 : r<1:=by
    apply (one_exponent_growth hβ hB hr cert).trans_le
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht
  have hRp : 0<R:=by dsimp [R]; linarith
  have hR1 : R<1:=by dsimp [R]; linarith
  have hrR : growthRate (normalizedA μ L α β) (normalizedB μ L α) β<R:=by
    change r<R
    dsimp [R]
    linarith
  obtain ⟨C,_,hΓ⟩:=exists_envelope_le_mul_pow hB hrR
  have hbound (n : ℕ) : ‖iterate (gradient f) α β x₀ n-a‖≤
      (Real.sqrt 2*C*‖x₀-a‖)*R^n:=by
    have hn:=Threshold.original_norm_le_envelope hf a hmin α β x₀ n
    have hm:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hΓ n) (Real.sqrt_nonneg 2)) (norm_nonneg (x₀-a))
    exact hn.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hm)
  have hlim : Tendsto (fun n : ℕ=>(Real.sqrt 2*C*‖x₀-a‖)*R^n) atTop (𝓝 0):=by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hRp.le hR1).const_mul (Real.sqrt 2*C*‖x₀-a‖)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)

theorem converges_of_zero_infeasible {μ L α β : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β))
    (h : ¬∃ (ν : Spectrum) (C : ℝ),Waves.MixtureFeasible ν
      (Waves.multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β 0) C 0)
    (a : E) (hmin : ∀ y,f a≤f y) (x₀ : E) :
    Tendsto (iterate (gradient f) α β x₀) atTop (𝓝 a) := by
  obtain ⟨cert⟩:=(infeasible_iff_strictCertificate _ _).mp h
  have hB : 0<normalizedB μ L α:=
    div_pos (mul_pos hα (sub_pos.mpr hf.mu_lt_L)) (by norm_num)
  have hc:=normalizedA_abs_add_B_lt hf.mu_pos hα hquad
  have hr:=rootRadius_lt_one hβ hβ1 (by linarith : |normalizedA μ L α β|<1+β)
  exact converges_of_certificate hf hα hβ (by norm_num)
    (by simpa only [Real.exp_zero] using hr) cert a hmin x₀

end polyak.General
