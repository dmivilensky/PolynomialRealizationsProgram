import jacobi.Reference.SharpSpectralDifferences
import jacobi.Reference.SpectralDisplacement

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The actual spatial slopes at both original spectra have their sharp
O(k^(1-gamma)) bound on every closed strip away from the singular
endpoint. Together with the sharpened norming and spectral-difference
bounds this makes the regularized derivative series summable.
Use: reference_slope_spectral_bound converts the original complex-frequency slope estimate to its exact original spectral-index scale for either sign of 1-gamma.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every fixed real power of the genuine reference phase has a uniform index-power bound.
Use: reference_slope_spectral_bound converts the original complex-frequency slope estimate to its exact original spectral-index scale for either sign of 1-gamma.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: use the true linear phase bounds; positive powers preserve their upper bound, while negative powers reverse their positive lower bound. -/
theorem reference_phase_power_bound {a : ℝ} (ha : -1<a) (p : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ k : ℕ,(jacobi.Bessel.phaseGrid a k)^p≤B*(k+1:ℝ)^p := by
  -- Both possible signs of the exponent are covered by one fixed positive sum of endpoint constants.
  obtain ⟨c,C,hc,hC,hphase⟩ := reference_phase_bounds ha
  refine ⟨c^p+C^p,by positivity,fun k => ?_⟩
  have hk : 0<(k+1:ℝ) := by positivity
  have hv := jacobi.Bessel.phaseGrid_pos ha k
  rcases le_or_gt 0 p with hp | hp
  · calc
      _ ≤ (C*(k+1:ℝ))^p := Real.rpow_le_rpow hv.le (hphase k).2 hp
      _ = C^p*(k+1:ℝ)^p := Real.mul_rpow hC.le hk.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
  · calc
      _ ≤ (c*(k+1:ℝ))^p := Real.rpow_le_rpow_of_nonpos (by positivity) (hphase k).1 hp.le
      _ = c^p*(k+1:ℝ)^p := Real.mul_rpow hc.le hk.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)

/-- The actual reference slope at the actual tau spectrum has its uniform sharp index bound away from zero.
Use: spectral_slope_bounds adds the proved genuine slope difference to control both original spectra in the regularized F derivative.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: specialize the actual high-frequency slope estimate at the original positive reference phase. Its squared energy is exactly tau_k-c_0, and the proved phase-power bound gives the printed index exponent. -/
theorem reference_slope_spectral_bound {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ k : ℕ in atTop,∀ t∈Icc d (1/2),
      |realSlope a (eigenvalue a k) t|≤B*(k+1:ℝ)^(1-gamma a) := by
  -- The threshold is derived from the actual positive linear phase growth.
  obtain ⟨A,hA,hbound⟩ := waveSlope_away_bound ha hd
  obtain ⟨B,hB,hpower⟩ := reference_phase_power_bound ha (1-gamma a)
  obtain ⟨c,C,hc,_hC,hphase⟩ := reference_phase_bounds ha
  obtain ⟨K,hK⟩ := exists_nat_gt ((max 1 (1/d))/c)
  refine ⟨A*B,mul_pos hA hB,?_⟩
  filter_upwards [eventually_ge_atTop K] with k hk t ht
  have hcast : (K:ℝ)≤k := by exact_mod_cast hk
  have hthr : max 1 (1/d)≤ jacobi.Bessel.phaseGrid a k := by
    have hh := (div_lt_iff₀ hc).mp hK
    exact (show max 1 (1/d)≤c*(k+1:ℝ) by nlinarith).trans (hphase k).1
  have hv := jacobi.Bessel.phaseGrid_pos ha k
  have hn : ‖((jacobi.Bessel.phaseGrid a k):ℂ)‖= jacobi.Bessel.phaseGrid a k := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨hd.trans_le ht.1,by linarith [ht.2]⟩
  have he : ((jacobi.Bessel.phaseGrid a k):ℂ)^2=(eigenvalue a k:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ) := by
    rw [eigenvalue_eq]
    change _=(((jacobi.Bessel.phaseGrid a k)^2+(1/4-a^2):ℝ):ℂ)-((1/4-a^2:ℝ):ℂ)
    push_cast
    ring
  have hh := hbound ((jacobi.Bessel.phaseGrid a k):ℂ) (by rw [hn]; exact hthr) t ht
  simp only [hn,Complex.ofReal_im,abs_zero,mul_zero,Real.exp_zero,mul_one] at hh
  have hr := Complex.abs_re_le_norm (solutionSlope a (eigenvalue a k:ℂ) t)
  rw [solutionSlope_eq_wave a ht' he] at hr
  change |(solutionSlope a (eigenvalue a k:ℂ) t).re|≤_
  rw [solutionSlope_eq_wave a ht' he]
  calc
    _ ≤ A*(jacobi.Bessel.phaseGrid a k)^(1-gamma a) := hr.trans hh
    _ ≤ A*(B*(k+1:ℝ)^(1-gamma a)) := mul_le_mul_of_nonneg_left (hpower k) hA.le
    _ = _ := by ring

/-- Both actual original spectral slopes have their sharp uniform index bound on every closed strip away from zero.
Use: bounds the derivative of each original spectral tensor and its difference in the summable regularized F derivative series.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the reference slope has the proved phase bound. The true target/reference slope difference is O(k^(-gamma-2)), hence also O(k^(1-gamma)); add the two estimates and enlarge the common constant. -/
theorem spectral_slope_bounds {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ k : ℕ in atTop,∀ t∈Icc d (1/2),
      |realSlope a (jacobi.Bessel.sigma a ha k) t|≤C*(k+1:ℝ)^(1-gamma a) ∧
      |realSlope a (eigenvalue a k) t|≤C*(k+1:ℝ)^(1-gamma a) := by
  -- The bound uses actual spectral slope differences, rather than differentiating a previous amplitude estimate.
  obtain ⟨A,hA,hreference⟩ := reference_slope_spectral_bound ha hd
  obtain ⟨B,hB,hdifference⟩ := spectral_slope_difference_sharp ha hd
  refine ⟨A+B,by positivity,?_⟩
  filter_upwards [hreference,hdifference] with k hk hdiff t ht
  have hkp : 0<(k+1:ℝ) := by positivity
  have hK : 1≤(k+1:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hscale : (k+1:ℝ)^(-gamma a)/(k+1:ℝ)^2≤(k+1:ℝ)^(1-gamma a) := by
    calc
      _ ≤ (k+1:ℝ)^(-gamma a) := div_le_self (by positivity) (by nlinarith)
      _ ≤ (k+1:ℝ)^(-gamma a)*(k+1:ℝ) := le_mul_of_one_le_right (by positivity) hK
      _ = _ := by rw [← Real.rpow_add_one hkp.ne']; congr 1; ring
  have hb : |realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t|≤B*(k+1:ℝ)^(1-gamma a) :=
    (hdiff t ht).trans (calc
      _ = B*((k+1:ℝ)^(-gamma a)/(k+1:ℝ)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hB.le)
  have htau := hk t ht
  constructor
  · have h := (abs_add_le (realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t)
        (realSlope a (eigenvalue a k) t)).trans (add_le_add hb htau)
    simpa only [sub_add_cancel,← add_mul,add_comm B A] using h
  · exact htau.trans (mul_le_mul_of_nonneg_right (by linarith : A≤A+B) (by positivity))

end
end jacobi.Reference
