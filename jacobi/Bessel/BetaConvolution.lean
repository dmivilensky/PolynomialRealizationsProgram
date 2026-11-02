import jacobi.Bessel.Convergence
import jacobi.Reference.BetaConvolution

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual normalized Bessel series admits beta convolution in its order,
with the genuine Gamma normalization. This supplies the original Poisson
integral from the proved half-integer cosine identity.
Source: Sonine's beta-integral formula for Bessel functions.
Use: evaluates the actual termwise integral in beta_convolution.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
open scoped Topology Interval
set_option backward.isDefEq.respectTransparency false

/-- Beta integration of every genuine normalized Bessel coefficient gives exactly the raised-order coefficient with the original beta scalar.
Use: evaluates the actual termwise integral in beta_convolution.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Sonine's integral, proved here from Euler's beta integral and the original convergent Bessel series.
Proof: the beta moment's Gamma(c+n) cancels the same genuine Bessel coefficient denominator. All canceled Gamma arguments have positive real part. -/
theorem beta_coefficient {c d : ℝ} (hc : 0<c) (hd : 0<d) (n : ℕ) :
    coefficient ((c:ℂ)-1) n*
      (Complex.Gamma ((c:ℂ)+n)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)+n))=
        (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))*
          coefficient ((c:ℂ)+(d:ℂ)-1) n := by
  rw [coefficient_formula,coefficient_formula,sub_add_cancel,sub_add_cancel]
  have hcn : Complex.Gamma ((c:ℂ)+n)≠0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [add_re,ofReal_re,natCast_re]; positivity)
  have hcd : Complex.Gamma ((c:ℂ)+(d:ℂ))≠0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [add_re,ofReal_re]; positivity)
  field_simp

/-- Beta convolution raises the order of the actual normalized entire Bessel function with its exact original beta normalization.
Use: the cosine identity at order -1/2 becomes the actual Bessel Poisson integral needed for the negative-axis characteristic comparison.
Article: jacobi, Appendix C.2 (norming ratios).
Source: Sonine's beta-integral formula, proved here by actual dominated integration.
Proof: the Bessel norm series at z is summable. Its terms multiplied
by the original singular beta weight dominate the genuine integrand
series uniformly on [0,1]. Lebesgue dominated convergence permits
termwise integration; the proved actual beta moments give the exact
raised-order Bessel coefficients and their original normalization. -/
theorem beta_convolution {c d : ℝ} (hc : 0<c) (hd : 0<d) (z : ℂ) :
    (∫ u in (0:ℝ)..1,(jacobi.Jacobi.weight (c-1) (d-1) u:ℂ)*
      normalized ((c:ℂ)-1) (z*(u:ℂ)))=
        (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))*
          normalized ((c:ℂ)+(d:ℂ)-1) z := by
  -- The original singular beta weight and the genuine entire Bessel norm series give one summable integrable majorant.
  let W : ℝ → ℝ := jacobi.Jacobi.weight (c-1) (d-1)
  let q : ℕ → ℂ := fun n => coefficient ((c:ℂ)-1) n*z^n
  let T : ℕ → ℝ → ℂ := fun n u => (W u:ℂ)*q n*(u:ℂ)^n
  have hq : Summable (fun n => ‖q n‖) := normalized_norm_summable _ z
  have hW : IntervalIntegrable W volume 0 1 := jacobi.Jacobi.weight_integrable (by linarith) (by linarith)
  have hWC := jacobi.Reference.Hypergeometric.beta_weight_integrable hc hd
  have hT (n : ℕ) : IntervalIntegrable (T n) volume 0 1 :=
    (hWC.mul_const (q n)).mul_continuousOn (by fun_prop)
  have hbound (n : ℕ) (u : ℝ) (hu : u∈Ι (0:ℝ) 1) : ‖T n u‖≤‖q n‖*W u := by
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
    have hW0 : 0≤W u := jacobi.Jacobi.weight_nonneg _ _ ⟨hu.1.le,hu.2⟩
    have hp : ‖(u:ℂ)^n‖≤1 := by
      rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu.1]
      exact pow_le_one₀ hu.1.le hu.2
    dsimp [T]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hW0]
    exact (mul_le_mul_of_nonneg_left hp (mul_nonneg hW0 (norm_nonneg _))).trans_eq (by ring)
  have hsum : HasSum (fun n => ∫ u in (0:ℝ)..1,T n u)
      (∫ u in (0:ℝ)..1,(W u:ℂ)*normalized ((c:ℂ)-1) (z*(u:ℂ))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n u => ‖q n‖*W u)
      (fun n => (hT n).def'.aestronglyMeasurable)
    · exact fun n => Eventually.of_forall (fun u hu => hbound n u hu)
    · exact Eventually.of_forall (fun _ _ => hq.mul_right _)
    · simpa only [tsum_mul_right] using hW.const_mul (∑' n,‖q n‖)
    · filter_upwards with u _
      have hs := (normalized_hasSum ((c:ℂ)-1) (z*(u:ℂ))).mul_left (W u:ℂ)
      convert! hs using 1
      funext n
      dsimp [T,q]
      rw [mul_pow]
      ring
  have ht (n : ℕ) : (∫ u in (0:ℝ)..1,T n u)=
      (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))*
        (coefficient ((c:ℂ)+(d:ℂ)-1) n*z^n) := by
    have he : T n=(fun u : ℝ => q n*((W u:ℂ)*(u:ℂ)^n)) := by funext u; dsimp [T]; ring
    rw [he,intervalIntegral.integral_const_mul,jacobi.Reference.Hypergeometric.beta_moment hc hd]
    dsimp [q]
    rw [mul_assoc,mul_comm (z^n),← mul_assoc,beta_coefficient hc hd]
    ring
  have hs := (normalized_hasSum ((c:ℂ)+(d:ℂ)-1) z).mul_left
    (Complex.Gamma (c:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((c:ℂ)+(d:ℂ)))
  exact hsum.unique (by simpa only [ht] using hs)

end
end jacobi.Bessel
