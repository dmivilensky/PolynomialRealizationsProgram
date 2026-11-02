import jacobi.Reference.PositiveIntegral
import jacobi.Reference.EndpointFrequency

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The literal defining integral gives the exact bound by the original
zero-frequency solution, with leading constant one. The wave on the
left is the same function used in every spectral and GL construction.
Source: the exponential cosine formula and the norm inequality for the
genuine Lebesgue integral of its positive weight.
Use: supplies the constant-one integrand comparison in sineIntegrand_norm and wave_cosine_domination.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The genuine complex cosine is bounded by the exact exponential of its imaginary part.
Use: supplies the constant-one integrand comparison in sineIntegrand_norm and wave_cosine_domination.
Article: jacobi, Lemma C.1.
Source: the classical exponential formula for cosine.
Proof: bound each of the two exponential norms by exp(abs(Im(w))) and divide their sum by two. -/
theorem cosine_norm_bound (z : ℂ) : ‖Complex.cos z‖≤Real.exp |z.im| := by
  -- Each true exponential has real exponent at most abs(Im(z)); the two-term average keeps leading constant one.
  have hh : ‖Complex.exp (z*Complex.I)+Complex.exp (-z*Complex.I)‖≤2*Real.exp |z.im| := by
    calc
      _ ≤ ‖Complex.exp (z*Complex.I)‖+‖Complex.exp (-z*Complex.I)‖ := norm_add_le _ _
      _ = Real.exp (-z.im)+Real.exp z.im := by simp [Complex.norm_exp]
      _ ≤ _ := by
        have h1 := Real.exp_le_exp.mpr (neg_le_abs z.im)
        have h2 := Real.exp_le_exp.mpr (le_abs_self z.im)
        linarith
  rw [Complex.cos,norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith)

/-- The actual sine integrand is bounded by its original positive density times the exact spatial exponential.
Use: proves the genuine integral domination in wave_cosine_domination, including singular endpoint exponents.
Article: jacobi, Lemma C.1.
Proof: the real cosine argument multiplier has absolute value at most
t on the whole integration interval. The exact cosine norm bound and
the nonnegative genuine sine density preserve the comparison. -/
theorem sineIntegrand_norm (g : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (omega : ℂ) {s : ℝ} (hs : s∈Icc (0:ℝ) t) :
    ‖sineIntegrand g t omega s‖≤sineWeight g t s*Real.exp (t*|omega.im|) := by
  -- The exponent uses the true imaginary frequency, without replacing it by the full frequency norm.
  have hd : |t-2*s|≤t := abs_le.mpr ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hc := cosine_norm_bound (((t-2*s:ℝ):ℂ)*omega)
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,abs_mul] at hc
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (abs_nonneg omega.im))
  change ‖(sineWeight g t s:ℂ)*Complex.cos (((t-2*s:ℝ):ℂ)*omega)‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sineWeight_nonneg g ht hs)]
  exact mul_le_mul_of_nonneg_left (hc.trans he) (sineWeight_nonneg g ht hs)

/-- The actual reference wave is dominated by its original zero-frequency solution with exactly the article's leading constant one.
Use: gives the full positive-weight bound in Reference solutions (b) and the exact original entire exponential type used in the parity contour argument.
Article: jacobi, Lemma C.1.
Proof: identify the actual wave with the original convergent beta
integral. Its positive outside factor multiplies the integral norm
inequality for the genuine positive density. The same actual density
integral is precisely the original zero-frequency value. -/
theorem wave_cosine_domination {a : ℝ} (ha : -1<a) (omega : ℂ) {t : ℝ}
    (ht : t∈Ico (0:ℝ) 1) :
    ‖wave a omega t‖≤(wave a 0 t).re*Real.exp (t*|omega.im|) := by
  -- The actual zero spatial endpoint is handled directly; every scalar canceled in the interior is positive.
  by_cases ht0 : t=0
  · subst t
    simp [wave,(weight_properties ha).2.1]
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  let P : ℝ := (betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)
  have hP : 0<P := mul_pos (inv_pos.mpr (betaNormalization_pos hg))
    (Real.rpow_pos_of_pos (div_pos
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht'.1)
        (by nlinarith [Real.pi_pos,ht'.2])) Real.pi_pos) _)
  have hzero : (wave a 0 t).re=P*(∫ s in (0:ℝ)..t,sineWeight (gamma a) t s) := by
    rw [wave_beta_integral ha 0 ht,betaWave_zero,Complex.ofReal_re]
  have hwave : wave a omega t=(P:ℂ)*(∫ s in (0:ℝ)..t,sineIntegrand (gamma a) t omega s) := by
    rw [wave_beta_integral ha omega ht]
    dsimp [betaWave,P]
    push_cast
    ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le ht.1
    (f := sineIntegrand (gamma a) t omega)
    (g := fun s => sineWeight (gamma a) t s*Real.exp (t*|omega.im|))
    (Eventually.of_forall fun s hs => sineIntegrand_norm (gamma a) ht' omega ⟨hs.1.le,hs.2⟩)
    ((sineWeight_integrable hg ht').mul_const (Real.exp (t*|omega.im|)))
  rw [intervalIntegral.integral_mul_const] at hb
  rw [hwave,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hP,hzero]
  exact (mul_le_mul_of_nonneg_left hb hP.le).trans_eq (by ring)

/-- The original zero-frequency solution is nonnegative on the closed half interval and has the printed uniform endpoint-power bound.
Use: completes all assertions involving the genuine positive majorant in Reference solutions (b).
Article: jacobi, Lemma C.1.
Proof: interior positivity is proved by the original beta integral;
the actual endpoint vanishes. Specialize the already proved genuine
endpoint-frequency bound to zero frequency. -/
theorem wave_zero_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ t∈Icc (0:ℝ) (1/2),0≤(wave a 0 t).re ∧ (wave a 0 t).re≤C*t^(gamma a) := by
  -- The bound is transferred to the real value of the same original wave, rather than a newly normalized function.
  obtain ⟨C,hC,hbound⟩ := wave_global_endpoint_bound ha
  refine ⟨C,hC,fun t ht => ⟨?_,?_⟩⟩
  · by_cases ht0 : t=0
    · subst t; simp [wave,(weight_properties ha).2.1]
    exact (wave_zero_pos ha ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),by linarith [ht.2]⟩).le
  · have hb := hbound (0:ℂ) t ht
    simp only [Complex.zero_im,abs_zero,mul_zero,Real.exp_zero,mul_one] at hb
    exact (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans hb

end
end jacobi.Reference
