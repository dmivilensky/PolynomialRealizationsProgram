import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's beta integral and Gamma recurrence, as formalized in mathlib.
Use: betaIntegral_norm_le bounds the actual beta integral, hence the Gamma quotient entering the contour lower bound.
-/
namespace jacobi.Complex
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- Positive real powers dominate the absolute beta integrand after a nonnegative real shift.
Use: betaIntegral_norm_le bounds the actual beta integral, hence the Gamma quotient entering the contour lower bound.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's beta integral.
Proof: the absolute value of a positive-base complex power depends only on its real exponent; increasing that exponent decreases powers on (0,1). -/
theorem betaIntegrand_norm_le {a b : ℝ} (z : ℂ) (hz : 0≤z.re)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    ‖(t:ℂ)^(z+(a:ℂ)-1)*(1-(t:ℂ))^((b:ℂ)-1)‖ ≤
      ‖(t:ℂ)^((a:ℂ)-1)*(1-(t:ℂ))^((b:ℂ)-1)‖ := by
  rw [norm_mul,norm_mul]
  apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_cpow_eq_rpow_re_of_pos ht.1,norm_cpow_eq_rpow_re_of_pos ht.1]
  simp only [sub_re,add_re,ofReal_re,one_re]
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by linarith)

/-- The actual beta integral is uniformly bounded after a right-half-plane shift in its first parameter.
Use: gammaRatio_norm_le converts this genuine integral majorant to a uniform Gamma quotient bound for the parity contour argument.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's beta integral.
Proof: integrate the pointwise absolute-value comparison; both absolute integrands are integrable because their real endpoint exponents exceed minus one. -/
theorem betaIntegral_norm_le {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (z : ℂ) (hz : 0≤z.re) :
    ‖betaIntegral (z+(a:ℂ)) (b:ℂ)‖ ≤
      ∫ t in (0:ℝ)..1,‖(t:ℂ)^((a:ℂ)-1)*(1-(t:ℂ))^((b:ℂ)-1)‖ := by
  -- Endpoint singularities are handled by the proved beta-integrability theorem.
  have hza : 0<(z+(a:ℂ)).re := by simp only [add_re,ofReal_re]; linarith
  have hai : 0<(a:ℂ).re := by simpa
  have hbi : 0<(b:ℂ).re := by simpa
  exact (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ)≤1)).trans
    (intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
      (betaIntegral_convergent hza hbi).norm (betaIntegral_convergent hai hbi).norm
      (fun _ ht => betaIntegrand_norm_le z hz ht))

/-- A Gamma quotient with increasing positive shifts is uniformly bounded on the closed right half-plane.
Use: gammaRatio_polynomial_bound removes the order restriction by the finite Gamma recurrence; the resulting growth bound feeds the contour lower estimate.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's beta integral and its Gamma evaluation.
Proof: the genuine Gamma quotient is the beta integral divided by the fixed positive Gamma(b-a); the preceding absolute integral bound is independent of z. -/
theorem gammaRatio_norm_le {a b : ℝ} (ha : 0<a) (hab : a<b) :
    ∃ C : ℝ,0<C ∧ ∀ z : ℂ,0≤z.re →
      ‖Gamma (z+(a:ℂ))/Gamma (z+(b:ℂ))‖≤C := by
  -- Positive real parts justify both Gamma cancellations in Euler's beta identity.
  let B : ℝ := ∫ t in (0:ℝ)..1,
    ‖(t:ℂ)^((a:ℂ)-1)*(1-(t:ℂ))^(((b-a:ℝ):ℂ)-1)‖
  have hd : 0<b-a := sub_pos.mpr hab
  have hG : 0<Real.Gamma (b-a) := Real.Gamma_pos_of_pos hd
  have hB : 0≤B := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
  refine ⟨B/Real.Gamma (b-a)+1,by positivity,fun z hz => ?_⟩
  have hza : 0<(z+(a:ℂ)).re := by simp only [add_re,ofReal_re]; linarith
  have hzb : 0<(z+(b:ℂ)).re := by simp only [add_re,ofReal_re]; linarith
  have hdc : 0<((b-a:ℝ):ℂ).re := by simpa
  have h := Gamma_mul_Gamma_eq_betaIntegral hza hdc
  rw [show z+(a:ℂ)+((b-a:ℝ):ℂ)=z+(b:ℂ) by push_cast; ring] at h
  have he : Gamma (z+(a:ℂ))/Gamma (z+(b:ℂ))=
      betaIntegral (z+(a:ℂ)) ((b-a:ℝ):ℂ)/Gamma ((b-a:ℝ):ℂ) := by
    apply (div_eq_div_iff (Gamma_ne_zero_of_re_pos hzb) (Gamma_ne_zero_of_re_pos hdc)).mpr
    exact h.trans (mul_comm _ _)
  rw [he,norm_div,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hG]
  exact (div_le_div_of_nonneg_right (betaIntegral_norm_le ha hd z hz) hG.le).trans (by
    change B/Real.Gamma (b-a)≤B/Real.Gamma (b-a)+1
    linarith)

/-- The finite Gamma recurrence evaluates the actual rising product at every right-half-plane point with positive initial shift.
Use: gammaRatio_polynomial_bound shifts any positive denominator argument far enough to apply the beta-integral bound.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's Gamma recurrence.
Proof: induct on the number of shifts, whose positive real parts exclude every pole and zero recurrence factor. -/
theorem gamma_shift_product {b : ℝ} (hb : 0<b) (z : ℂ) (hz : 0≤z.re) (n : ℕ) :
    Gamma (z+(b:ℂ)+(n:ℂ))=Gamma (z+(b:ℂ))*∏ j∈Finset.range n,(z+(b:ℂ)+(j:ℂ)) := by
  -- Every shifted argument has positive real part, so each recurrence step is valid at the actual Gamma value.
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z+(b:ℂ)+(n:ℂ)≠0 := by
      apply ne_of_apply_ne Complex.re
      simp only [add_re,ofReal_re,natCast_re,zero_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [Nat.cast_add,Nat.cast_one,← add_assoc,Gamma_add_one _ hn,ih,Finset.prod_range_succ]
    ring

/-- Every Gamma quotient with fixed positive real shifts has a uniform polynomial growth bound in the closed right half-plane.
Use: the Phragmen--Lindelof argument for the normalized quotient needs only this crude growth, before recovering the sharp power law used for Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's beta integral and finite Gamma recurrence.
Proof: shift the denominator by a sufficiently large integer. The beta integral bounds the shifted quotient; the recurrence leaves a finite product, with every factor bounded by a constant times 1+norm(z). -/
theorem gammaRatio_polynomial_bound {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∃ C : ℝ,0<C ∧ ∃ n : ℕ,∀ z : ℂ,0≤z.re →
      ‖Gamma (z+(a:ℂ))/Gamma (z+(b:ℂ))‖≤C*(1+‖z‖)^n := by
  -- The shift is fixed once for the two parameters, uniformly over the entire half-plane.
  obtain ⟨n,hn⟩ := exists_nat_gt (a-b)
  obtain ⟨C,hC,hbound⟩ := gammaRatio_norm_le ha (show a<b+(n:ℝ) by linarith)
  refine ⟨C*(b+(n:ℝ)+1)^n,by positivity,n,fun z hz => ?_⟩
  let P : ℂ := ∏ j∈Finset.range n,(z+(b:ℂ)+(j:ℂ))
  have hzb : 0<(z+(b:ℂ)).re := by simp only [add_re,ofReal_re]; linarith
  have hzbn : 0<(z+((b+(n:ℝ):ℝ):ℂ)).re := by
    simp only [add_re,ofReal_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hrec : Gamma (z+((b+(n:ℝ):ℝ):ℂ))=Gamma (z+(b:ℂ))*P := by
    simpa only [P,Complex.ofReal_add,Complex.ofReal_natCast,add_assoc] using gamma_shift_product hb z hz n
  have he : Gamma (z+(a:ℂ))/Gamma (z+(b:ℂ))=
      Gamma (z+(a:ℂ))/Gamma (z+((b+(n:ℝ):ℝ):ℂ))*P := by
    apply (div_eq_iff (Gamma_ne_zero_of_re_pos hzb)).mpr
    rw [mul_assoc,mul_comm P _,← hrec,div_mul_cancel₀ _ (Gamma_ne_zero_of_re_pos hzbn)]
  have hP : ‖P‖≤((b+(n:ℝ)+1)*(1+‖z‖))^n := by
    dsimp [P]
    rw [norm_prod]
    calc
      _ ≤ ∏ _j∈Finset.range n,((b+(n:ℝ)+1)*(1+‖z‖)) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j hj
        have hjn : (j:ℝ)≤n := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
        have hreal : 0≤b+(j:ℝ) := by positivity
        have heq : z+(b:ℂ)+(j:ℂ)=z+((b+(j:ℝ):ℝ):ℂ) := by push_cast; ring
        rw [heq]
        calc
          _ ≤ ‖z‖+‖((b+(j:ℝ):ℝ):ℂ)‖ := norm_add_le _ _
          _ = ‖z‖+(b+(j:ℝ)) := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hreal]
          _ ≤ (b+(n:ℝ)+1)*(1+‖z‖) := by nlinarith [norm_nonneg z]
      _ = _ := by simp
  rw [he,norm_mul]
  exact (mul_le_mul (hbound z hz) hP (norm_nonneg _) hC.le).trans_eq (by rw [mul_pow]; ring)

end
end jacobi.Complex
