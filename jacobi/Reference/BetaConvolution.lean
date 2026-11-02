import jacobi.Reference.BetaIntegral
import jacobi.Reference.HypergeometricBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Beta convolution of the genuine Gauss series raises its denominator
parameter. Singular endpoint weights are integrated in their original
Lebesgue sense, with one summable majorant proving the interchange.
Source: Euler's beta integral and the hypergeometric fractional-integral
identity; both applied to actual convergent functions here.
Use: evaluates every term of the genuine beta-convolved Gauss series in beta_convolution.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex Polynomial
open scoped Topology Interval
set_option backward.isDefEq.respectTransparency false

/-- A polynomial moment of the actual beta weight has exactly its original Gamma quotient.
Use: evaluates every term of the genuine beta-convolved Gauss series in beta_convolution.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Euler's beta--Gamma identity, reused from Reference.BetaIntegral.
Proof: on the open integration interval combine the positive-base
powers to raise the first beta parameter by the actual integer degree.
The already proved original Jacobi-weight integral gives the quotient;
the endpoints have zero measure, including for singular powers. -/
theorem beta_moment {c d : ℝ} (hc : 0<c) (hd : 0<d) (n : ℕ) :
    (∫ u in (0:ℝ)..1,(jacobi.Jacobi.weight (c-1) (d-1) u:ℂ)*(u:ℂ)^n)=
      Complex.Gamma ((c:ℂ)+n)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)+n) := by
  -- Power multiplication is used only at positive interior bases, never at a singular totalized endpoint.
  have he : (∫ u in (0:ℝ)..1,(jacobi.Jacobi.weight (c-1) (d-1) u:ℂ)*(u:ℂ)^n)=
      ∫ u in (0:ℝ)..1,(jacobi.Jacobi.weight (c-1+n) (d-1) u:ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    rw [← Complex.ofReal_pow,← Complex.ofReal_mul]
    congr 1
    unfold jacobi.Jacobi.weight
    rw [Real.rpow_add hu.1,Real.rpow_natCast]
    ring
  rw [he,intervalIntegral.integral_ofReal,jacobi_weight_integral (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)]
  have h1 : c-1+(n:ℝ)+1=c+n := by ring
  have h2 : c-1+(n:ℝ)+(d-1)+2=c+d+n := by ring
  rw [h1,h2,sub_add_cancel]
  push_cast
  rw [← Complex.Gamma_ofReal,← Complex.Gamma_ofReal,← Complex.Gamma_ofReal]
  push_cast
  rfl

/-- Beta integration converts every actual Gauss coefficient to the same coefficient with the raised denominator parameter.
Use: identifies the summed beta convolution with the original hypergeometric function, including terminating numerator parameters.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: Euler's Gamma recurrence and the Gamma/Pochhammer identity in mathlib.
Proof: express both positive denominator Pochhammer symbols by their
genuine Gamma ratios. Their shared numerator factors and the moment's
Gamma(c+n) cancel, leaving precisely the raised-denominator coefficient. -/
theorem beta_coefficient (a b : ℂ) {c d : ℝ} (hc : 0<c) (hd : 0<d) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b (c:ℂ) n*
      (Complex.Gamma ((c:ℂ)+n)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)+n))=
        (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))*
          ordinaryHypergeometricCoefficient a b ((c:ℂ)+(d:ℂ)) n := by
  -- Positive denominator parameters exclude every Gamma and rising-factorial pole independently of a and b.
  have hnon {s : ℂ} (hs : 0<s.re) (j : ℕ) : s≠-(j:ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp only [neg_re,natCast_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hcn : Complex.Gamma ((c:ℂ)+n)≠0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [add_re,ofReal_re,natCast_re]; positivity)
  have hcdn : Complex.Gamma ((c:ℂ)+(d:ℂ)+n)≠0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [add_re,ofReal_re,natCast_re]; positivity)
  have hC : Complex.Gamma (c:ℂ)≠0 := Complex.Gamma_ne_zero_of_re_pos hc
  have hCD : Complex.Gamma ((c:ℂ)+(d:ℂ))≠0 := Complex.Gamma_ne_zero_of_re_pos (by simpa only [add_re,ofReal_re] using add_pos hc hd)
  unfold ordinaryHypergeometricCoefficient
  rw [← Complex.Gamma_add_nat_div_Gamma_eq (c:ℂ) (hnon hc),
    ← Complex.Gamma_add_nat_div_Gamma_eq ((c:ℂ)+(d:ℂ)) (hnon (by simpa only [add_re,ofReal_re] using add_pos hc hd))]
  field_simp [hcn,hcdn,hC,hCD]

/-- The literal complex embedding of the singular real beta weight is genuinely interval integrable.
Use: supplies measurability and the actual integrable majorant for beta_convolution, without replacing the improper integrals by formal beta symbols.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: use the already proved full real Jacobi-weight convergence and compose with the continuous real-to-complex linear map. -/
theorem beta_weight_integrable {c d : ℝ} (hc : 0<c) (hd : 0<d) :
    IntervalIntegrable (fun u : ℝ => (jacobi.Jacobi.weight (c-1) (d-1) u:ℂ)) volume 0 1 := by
  rw [intervalIntegrable_iff]
  exact Complex.ofRealCLM.integrable_comp
    (jacobi.Jacobi.weight_integrable (by linarith : -1<c-1) (by linarith : -1<d-1)).def'

/-- Beta convolution of the actual convergent Gauss function raises its denominator by the positive beta exponent, with the exact original normalization.
Use: evaluates the fractional integral of the cosine hypergeometric representation in the article's defining beta integral for f.
Article: jacobi, Lemma C.1.
Source: Euler's hypergeometric fractional-integral identity, proved here by actual dominated termwise integration.
Proof: each genuine series term is integrable against the original
singular beta weight. Its norm is bounded by that weight times the
summable Gauss norm series at |z|. Dominated convergence permits the
actual interchange. The proved beta moment and coefficient identity
then give the original raised-denominator Gauss series. -/
theorem beta_convolution (a b : ℂ) {c d : ℝ} (hc : 0<c) (hd : 0<d)
    {z : ℂ} (hz : ‖z‖<1) :
    (∫ u in (0:ℝ)..1,(jacobi.Jacobi.weight (c-1) (d-1) u:ℂ)*
      ordinaryHypergeometric a b (c:ℂ) (z*(u:ℂ)))=
        (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))*
          ordinaryHypergeometric a b ((c:ℂ)+(d:ℂ)) z := by
  -- The original singular weight supplies one integrable bound for the whole genuine series.
  let W : ℝ → ℝ := jacobi.Jacobi.weight (c-1) (d-1)
  let q : ℕ → ℂ := fun n => ordinaryHypergeometricCoefficient a b (c:ℂ) n*z^n
  let T : ℕ → ℝ → ℂ := fun n u => (W u:ℂ)*q n*(u:ℂ)^n
  have hq : Summable (fun n => ‖q n‖) := summable_norm hz
  have hW : IntervalIntegrable W volume 0 1 :=
    jacobi.Jacobi.weight_integrable (by linarith) (by linarith)
  have hWC := beta_weight_integrable hc hd
  have hT (n : ℕ) : IntervalIntegrable (T n) volume 0 1 :=
    (hWC.mul_const (q n)).mul_continuousOn (by fun_prop)
  have hbound (n : ℕ) (u : ℝ) (hu : u∈Ι (0:ℝ) 1) : ‖T n u‖≤‖q n‖*W u := by
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
    have hu' : u∈Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2⟩
    have hW0 : 0≤W u := jacobi.Jacobi.weight_nonneg _ _ hu'
    have hp : ‖(u:ℂ)^n‖≤1 := by
      rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu'.1]
      exact pow_le_one₀ hu'.1 hu'.2
    dsimp [T]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hW0]
    exact (mul_le_mul_of_nonneg_left hp (mul_nonneg hW0 (norm_nonneg _))).trans_eq (by ring)
  have hsum : HasSum (fun n => ∫ u in (0:ℝ)..1,T n u)
      (∫ u in (0:ℝ)..1,(W u:ℂ)*ordinaryHypergeometric a b (c:ℂ) (z*(u:ℂ))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n u => ‖q n‖*W u)
      (fun n => (hT n).def'.aestronglyMeasurable)
    · exact fun n => Eventually.of_forall (fun u hu => hbound n u hu)
    · exact Eventually.of_forall (fun _ _ => hq.mul_right _)
    · simpa only [tsum_mul_right] using hW.const_mul (∑' n,‖q n‖)
    · filter_upwards with u hu
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
      have hu' : u∈Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2⟩
      have hx : ‖z*(u:ℂ)‖<1 := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu'.1]
        exact (mul_le_of_le_one_right (norm_nonneg _) hu'.2).trans_lt hz
      have hs := (summable_norm (u := a) (v := b) (c := (c:ℂ)) hx).of_norm.hasSum
      have hs' : HasSum (fun n => ordinaryHypergeometricCoefficient a b (c:ℂ) n*(z*(u:ℂ))^n)
          (ordinaryHypergeometric a b (c:ℂ) (z*(u:ℂ))) := by
        simpa only [ordinaryHypergeometric_eq_tsum,smul_eq_mul] using hs
      convert hs'.mul_left (W u:ℂ) using 1
      funext n
      dsimp [T,q]
      rw [mul_pow]
      ring
  have hterms (n : ℕ) : (∫ u in (0:ℝ)..1,T n u)=
      (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))*
        (ordinaryHypergeometricCoefficient a b ((c:ℂ)+(d:ℂ)) n*z^n) := by
    have he : T n=(fun u : ℝ => q n*((W u:ℂ)*(u:ℂ)^n)) := by funext u; dsimp [T]; ring
    rw [he,intervalIntegral.integral_const_mul,beta_moment hc hd]
    dsimp [q]
    rw [mul_assoc,mul_comm (z^n),← mul_assoc,beta_coefficient a b hc hd]
    ring
  have hs := (summable_norm (u := a) (v := b) (c := (c:ℂ)+(d:ℂ)) hz).of_norm.hasSum.mul_left
    (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))
  have ht : HasSum (fun n => ∫ u in (0:ℝ)..1,T n u)
      ((Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))*
        ordinaryHypergeometric a b ((c:ℂ)+(d:ℂ)) z) := by
    simpa only [hterms,ordinaryHypergeometric_eq_tsum,smul_eq_mul] using hs
  exact hsum.unique ht

end
end jacobi.Reference.Hypergeometric
