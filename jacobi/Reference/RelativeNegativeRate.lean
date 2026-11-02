import jacobi.Reference.RelativeCharacteristic
import jacobi.Reference.SpectralDisplacement

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The genuine original relative characteristic differs from one by
O(y^-2) on c_0-y^2. Absolute spectral displacement and the already
proved exact relative product give the bound directly. This retains
the printed normalization needed to exclude a residual Robin term.
Use: relative_characteristic_negative_rate applies the proved original relative product with its genuine nonzero denominator checked.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original Bessel characteristic has no zero on the actual shifted negative-energy path.
Use: relative_characteristic_negative_rate applies the proved original relative product with its genuine nonzero denominator checked.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: every original sigma_k is strictly above c_0, whereas c_0-y^2 is at most c_0. The proved exhaustive complex zero set therefore excludes a zero. -/
theorem characteristicSigma_shifted_negative_ne_zero (a : ℝ) (ha : -1<a) (y : ℝ) :
    characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)≠0 := by
  intro hz
  obtain ⟨k,hk⟩ := (characteristicSigma_zero_iff ha _).mp hz
  have he := Complex.ofReal_injective hk
  have hg := jacobi.Bessel.sigma_above_correction ha k
  change jacobi.Jacobi.endpointCorrection a< jacobi.Bessel.sigma a ha k at hg
  nlinarith [sq_nonneg y]

/-- The actual normalized relative characteristic has its full original inverse-square negative-frequency error bound.
Use: relative_characteristic_negative_scaled_error proves the zero first-order correction used to identify the actual remaining midpoint boundary parameter as Neumann.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: each true relative factor differs from one by at most abs(delta_k)/y^2 because sigma_k>c_0. Sum the actual absolutely convergent displacement series and apply the proved infinite-product Lipschitz inequality with its unchanged normalization one. -/
theorem relative_characteristic_negative_rate (a : ℝ) (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∀ y:ℝ,1≤y →
      ‖characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
        characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-1‖≤C/y^2 := by
  -- Absolute convergence is established for the actual original factors before applying the product norm estimate.
  have hs := spectralDisplacement_summable ha
  let D := (∑' k,|spectralDisplacement a ha k|)+1
  have hsum : 0≤∑' k,|spectralDisplacement a ha k| := tsum_nonneg (fun _ => abs_nonneg _)
  have hD : 0<D := by dsimp [D]; linarith
  refine ⟨Real.exp D*D,by positivity,fun y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  let d : ℕ → ℂ := fun k => (((eigenvalue a k- jacobi.Bessel.sigma a ha k)/
    (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2):ℝ):ℂ)
  have hb (k : ℕ) : ‖d k‖≤|spectralDisplacement a ha k|/y^2 := by
    have hg := jacobi.Bessel.sigma_above_correction ha k
    change jacobi.Jacobi.endpointCorrection a< jacobi.Bessel.sigma a ha k at hg
    have hden : y^2≤ jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2 := by linarith
    dsimp [d]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,
      abs_of_pos (show 0< jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2 by nlinarith),abs_sub_comm]
    change |spectralDisplacement a ha k|/(jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2)≤_
    exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hyp) hden
  have hds : Summable (fun k => ‖d k‖) := (hs.div_const (y^2)).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hbound : (∑' k,‖d k‖)≤D/y^2 := by
    calc
      _ ≤ ∑' k,|spectralDisplacement a ha k|/y^2 := hds.tsum_le_tsum hb (hs.div_const _)
      _ = (∑' k,|spectralDisplacement a ha k|)/y^2 := tsum_div_const
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp [D]; linarith) (sq_nonneg y)
  have hsmall : (∑' k,‖d k‖)≤D := hbound.trans (div_le_self hD.le (by nlinarith))
  have hprod := jacobi.Bessel.infinite_product_lipschitz d (fun _ => 0) hds (by simp)
  simp only [add_zero,tprod_one,norm_zero,tsum_zero,sub_zero] at hprod
  have he : characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)=∏' k,(1+d k) := by
    rw [relative_characteristic_product ha _ (characteristicSigma_shifted_negative_ne_zero a ha y)]
    apply tprod_congr
    intro k
    have hg := jacobi.Bessel.sigma_above_correction ha k
    change jacobi.Jacobi.endpointCorrection a< jacobi.Bessel.sigma a ha k at hg
    have hden : jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a+y^2≠0 := by nlinarith [sq_nonneg y]
    dsimp [d]
    push_cast
    have hd : (jacobi.Bessel.sigma a ha k:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ)+(y:ℂ)^2≠0 := by exact_mod_cast hden
    rw [show (jacobi.Bessel.sigma a ha k:ℂ)-((jacobi.Jacobi.endpointCorrection a:ℂ)-(y:ℂ)^2)=
      (jacobi.Bessel.sigma a ha k:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ)+(y:ℂ)^2 by ring]
    field_simp [hd]
    ring
  rw [he]
  exact hprod.trans ((mul_le_mul (Real.exp_le_exp.mpr hsmall) hbound
    (tsum_nonneg (fun _ => norm_nonneg _)) (Real.exp_pos _).le).trans_eq (by ring))

/-- The actual original relative characteristic has zero first-order negative-frequency correction.
Use: the exact mixed characteristic identity and the genuine improved midpoint asymptotics exclude the actual residual Robin parameter in Proposition C.2.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: multiplying the proved actual inverse-square error by the positive frequency leaves C/y, whose genuine limit is zero. -/
theorem relative_characteristic_negative_scaled_error (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => (y:ℂ)*(characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)-1)) atTop (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := relative_characteristic_negative_rate a ha
  apply squeeze_zero_norm' ?_ (tendsto_id.const_div_atTop C)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  exact (mul_le_mul_of_nonneg_left (hbound y hy) hyp.le).trans_eq (by dsimp only [id_eq]; field_simp [hyp.ne'])

end
end jacobi.Reference
