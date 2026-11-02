import jacobi.Reference.NormingRatios
import jacobi.Reference.IndexMajorant

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The actual logarithms of the original norming factors have a uniform
summable majorant. Its full sum proves the printed inverse-square bound
for every original norming ratio, without a large-index exception.
Use: estimates actual norming-factor logarithms without any smallness assumption or exceptional finite prefix.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology

/-- Positive gap ratios have a global logarithm bound from the common lower gap bound and the numerator displacement.
Use: estimates actual norming-factor logarithms without any smallness assumption or exceptional finite prefix.
Article: jacobi, Appendix C.2 (norming ratios).
Source: the classical inequalities log(x)<=x-1 and 1-1/x<=log(x), proved in mathlib.
Proof: apply the two classical inequalities to the positive ratio. Both
its deviation from one and the inverse deviation are bounded by the
same displacement divided by the common positive gap lower bound. -/
theorem log_gap_ratio_le {u v d e : ℝ} (hd : 0<d) (hu : d≤u) (hv : d≤v)
    (he : |u-v|≤e) : |Real.log (u/v)|≤e/d := by
  -- Using the inverse ratio avoids a local log expansion and treats all genuine indices uniformly.
  have hup : 0<u := hd.trans_le hu
  have hvp : 0<v := hd.trans_le hv
  have hep : 0≤e := (abs_nonneg _).trans he
  have hratio : 0<u/v := div_pos hup hvp
  have hforward : |u/v-1|≤e/d := by
    rw [div_sub_one hvp.ne',abs_div,abs_of_pos hvp]
    exact div_le_div₀ hep he hd hv
  have hbackward : |(u/v)⁻¹-1|≤e/d := by
    rw [inv_div,div_sub_one hup.ne',abs_div,abs_of_pos hup,abs_sub_comm]
    exact div_le_div₀ hep he hd hu
  apply abs_le.mpr
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hratio
    have hh := (le_abs_self ((u/v)⁻¹-1)).trans hbackward
    linarith
  · exact (Real.log_le_sub_one_of_pos hratio).trans ((le_abs_self _).trans hforward)

/-- A fixed common positive spectral gap gives the exact rational logarithm majorant for every actual off-diagonal norming factor.
Use: feeds the translated p-series estimate into the actual original norming-product bound.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: order the indices, bound the difference of genuine displacements
by the two proved McMahon errors and apply the global positive-gap
logarithm inequality. Reverse ordering leaves the actual ratio unchanged. -/
theorem normingFactor_log_majorant {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k l : ℕ,k≠l →
      |Real.log (normingFactor a ha k l)|≤
        B*((1/(k+1:ℝ)^2+1/(l+1:ℝ)^2)/|(l+1:ℝ)^2-(k+1:ℝ)^2|) := by
  -- All gap and displacement constants are conclusions about the actual original spectra.
  obtain ⟨C,c,hC,hc,he,ht,hs⟩ := spectral_product_inputs ha
  refine ⟨C/c,by positivity,?_⟩
  have hordered : ∀ k l : ℕ,k<l →
      |Real.log (normingFactor a ha k l)|≤
        (C/c)*((1/(k+1:ℝ)^2+1/(l+1:ℝ)^2)/|(l+1:ℝ)^2-(k+1:ℝ)^2|) := by
    intro k l hkl
    have hcast : (k+1:ℝ)<l+1 := by exact_mod_cast Nat.add_lt_add_right hkl 1
    have hx : 0<(k+1:ℝ) := by positivity
    have hq : 0<(l+1:ℝ)^2-(k+1:ℝ)^2 := by nlinarith
    have hn : |(eigenvalue a l-eigenvalue a k)-
        (jacobi.Bessel.sigma a ha l- jacobi.Bessel.sigma a ha k)|≤
        C*((1/(k+1:ℝ)^2)+(1/(l+1:ℝ)^2)) := by
      calc
        _ = |(jacobi.Bessel.sigma a ha k-eigenvalue a k)-(jacobi.Bessel.sigma a ha l-eigenvalue a l)| := by congr 1; ring
        _ ≤ |jacobi.Bessel.sigma a ha k-eigenvalue a k|+|jacobi.Bessel.sigma a ha l-eigenvalue a l| := abs_sub _ _
        _ ≤ C/(k+1:ℝ)^2+C/(l+1:ℝ)^2 := add_le_add (he k) (he l)
        _ = _ := by ring
    have hh := log_gap_ratio_le (mul_pos hc hq) (ht k l hkl.le) (hs k l hkl.le) hn
    simp only [normingFactor,hkl.ne',ite_false,abs_of_pos hq]
    exact hh.trans_eq (by field_simp)
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hordered k l h
  · have hr : normingFactor a ha k l=normingFactor a ha l k := by
      simp only [normingFactor,h.ne,h.ne',ite_false]
      rw [show eigenvalue a l-eigenvalue a k= -(eigenvalue a k-eigenvalue a l) by ring,
        show jacobi.Bessel.sigma a ha l- jacobi.Bessel.sigma a ha k=
          -(jacobi.Bessel.sigma a ha k- jacobi.Bessel.sigma a ha l) by ring,neg_div_neg_eq]
    rw [hr,add_comm (1/(k+1:ℝ)^2),abs_sub_comm]
    exact hordered l k h

/-- The original norming-factor logarithms admit one summable inverse-square majorant, uniform in the original index.
Use: bounds the full logarithm sum of rho_k by a fixed constant times (k+1)^-2.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: apply the single rational two-series inequality away from the
omitted diagonal. On the diagonal the original factor is one, and the
same nonnegative majorant applies. -/
theorem normingFactor_log_bound {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k l : ℕ,
      |Real.log (normingFactor a ha k l)|≤
        B*((2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2) := by
  -- Positivity permits multiplication of the actual rational spectral-error bound.
  obtain ⟨B,hB,hbound⟩ := normingFactor_log_majorant ha
  refine ⟨B,hB,fun k l => ?_⟩
  by_cases hkl : k=l
  · subst l
    simp only [normingFactor,ite_true,Real.log_one,abs_zero]
    dsimp [distanceMajorant]
    positivity
  · exact (hbound k l hkl).trans (mul_le_mul_of_nonneg_left (inverse_square_gap_majorant hkl) hB.le)

/-- The actual norming ratios satisfy the printed inverse-square logarithm estimate for every original index.
Use: supplies the uniform original spectral-weight control needed by the Gel'fand--Levitan kernel.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: express the logarithm of the genuinely convergent positive
product as its actual logarithm series. Its absolute sum is bounded by
the uniform translated p-series majorant, whose total mass is at most
eight times the fixed positive inverse-square series. -/
theorem normingRatio_log_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k,|Real.log (normingRatio a ha k)|≤C/(k+1:ℝ)^2 := by
  -- Every convergence and positivity premise was already proved for the literal original product.
  obtain ⟨B,hB,hbound⟩ := normingFactor_log_bound ha
  let S : ℝ := ∑' l:ℕ,1/(l+1:ℝ)^2
  have hs : Summable (fun l:ℕ => 1/(l+1:ℝ)^2) := by
    simpa only [one_pow] using jacobi.Bessel.inverse_square_majorant_summable 1
  have hS : 0<S := by
    have hh := hs.le_tsum 0 (fun l _ => by positivity)
    norm_num only [Nat.cast_zero,zero_add,one_pow,div_one] at hh
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hh
  refine ⟨8*B*S,by positivity,fun k => ?_⟩
  have hm : Summable (fun l:ℕ => B*((2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2)) := by
    simpa only [mul_one_div] using
      (((hs.mul_left 2).add ((distanceMajorant_summable k).mul_left 3)).div_const ((k+1:ℝ)^2)).mul_left B
  have hlogs := normingFactor_log_summable ha k
  have habs : Summable (fun l => |Real.log (normingFactor a ha k l)|) := hlogs.abs
  have he : Real.log (normingRatio a ha k)=∑' l,Real.log (normingFactor a ha k l) := by
    rw [normingRatio,← Real.rexp_tsum_eq_tprod (normingFactor_pos ha k) hlogs,Real.log_exp]
  rw [he]
  have hnorm := norm_tsum_le_tsum_norm hlogs.norm
  simp only [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  apply (habs.tsum_le_tsum (hbound k) hm).trans
  have hsum : (∑' l:ℕ,(2/(l+1:ℝ)^2+3*distanceMajorant k l))=
      2*S+3*(∑' l,distanceMajorant k l) := by
    have hh := (hs.mul_left 2).tsum_add ((distanceMajorant_summable k).mul_left 3)
    rw [tsum_mul_left,tsum_mul_left] at hh
    simpa only [mul_one_div,S] using hh
  rw [tsum_mul_left,tsum_div_const,hsum,← mul_div_assoc]
  have hdist := distanceMajorant_tsum_le k
  dsimp [S] at *
  apply (div_le_div_iff_of_pos_right (by positivity : 0<(k+1:ℝ)^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hdist (show 0≤3*B by positivity)]


/-- The real exponential remainder is bounded globally by its argument times the exponential of its absolute value.
Use: converts the genuine logarithmic norming-ratio bound into a bound for the actual weights themselves.
Article: jacobi, Proposition C.4.
Source: the exponential-series remainder inequality, proved in mathlib.
Proof: specialize the community complex exponential tail bound to degree one and cast the actual real argument. -/
theorem exp_sub_one_bound (x : ℝ) : |Real.exp x-1|≤|x| * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x:ℂ) 1
  norm_num only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,
    div_one,pow_one] at h
  simpa only [← Complex.ofReal_exp,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] using h

/-- All actual norming ratios are bounded above and uniformly away from zero, and their deviations from one decay quadratically.
Use: supplies the original positive spectral weights and the uniform weight perturbation used by the GL kernel series.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the actual positive product equals the exponential of its real
logarithm. The proved inverse-square logarithm bound is also a constant
bound, so monotonicity of exp gives both positive bounds. The global
exponential remainder inequality gives the inverse-square deviation. -/
theorem normingRatio_bounds {a : ℝ} (ha : -1<a) :
    ∃ c C D : ℝ,0<c ∧ 0<C ∧ 0<D ∧ ∀ k,
      c≤normingRatio a ha k ∧ normingRatio a ha k≤C ∧
        |normingRatio a ha k-1|≤D/(k+1:ℝ)^2 := by
  -- The constants apply to every true original spectral weight, including the finite small-index prefix.
  obtain ⟨L,hL,hlog⟩ := normingRatio_log_bound ha
  refine ⟨Real.exp (-L),Real.exp L,L*Real.exp L,Real.exp_pos _,Real.exp_pos _,by positivity,fun k => ?_⟩
  have hsq : 1≤(k+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have habs : |Real.log (normingRatio a ha k)|≤L :=
    (hlog k).trans (div_le_self hL.le hsq)
  have hpos := (normingRatio_properties ha k).2
  have he : Real.exp (Real.log (normingRatio a ha k))=normingRatio a ha k := Real.exp_log hpos
  refine ⟨?_,?_,?_⟩
  · rw [← he]
    exact Real.exp_le_exp.mpr (abs_le.mp habs).1
  · rw [← he]
    exact Real.exp_le_exp.mpr (abs_le.mp habs).2
  · rw [← he]
    apply (exp_sub_one_bound _).trans
    have hm := mul_le_mul (hlog k) (Real.exp_le_exp.mpr habs)
      (Real.exp_pos _).le (by positivity : 0≤L/(k+1:ℝ)^2)
    simpa only [div_mul_eq_mul_div] using hm

/-- The genuine original norming ratios tend to one along the original spectral enumeration.
Use: fixes the normalization at high frequency in the source GL and finite-to-continuum limits.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the proved actual inverse-square deviation is bounded by a term of a genuine summable series, hence tends to zero. -/
theorem normingRatio_tendsto_one {a : ℝ} (ha : -1<a) :
    Tendsto (normingRatio a ha) atTop (𝓝 1) := by
  -- A genuine summable majorant supplies the zero limit; no asymptotic premise is introduced.
  obtain ⟨c,C,D,_,_,_,hb⟩ := normingRatio_bounds ha
  have hsum : Summable (fun k:ℕ => D/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left D
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => by
    simpa only [Real.norm_eq_abs] using (hb k).2.2) hsum.tendsto_atTop_zero

end
end jacobi.Reference
