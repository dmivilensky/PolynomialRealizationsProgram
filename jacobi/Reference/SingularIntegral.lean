import jacobi.Reference.AbelIntegral

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
Every endpoint singularity is treated by genuine Lebesgue integrability.
The cosine substitution transports the original beta weight, rather than
assuming continuity of a weight with negative endpoint exponent.
Source: Euler's beta integral and monotone change of variables.
Use: establishes convergence before applying the angular change of variables in mehler_integrable.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- A continuous multiplier of the actual Abel weight is genuinely integrable throughout gamma>0.
Use: establishes convergence before applying the angular change of variables in mehler_integrable.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: Euler's integrable beta weight with parameters 1/2 and gamma.
Proof: rescale the interval by its positive length. The exact scaling
identity reduces the original singular endpoints to the integrable beta
weight times a continuous multiplier on the compact unit interval. -/
theorem abel_integrable {g x : ℝ} (hg : 0<g) (hx : 0<x) {F : ℝ → ℂ}
    (hF : ContinuousOn F (Icc (0:ℝ) x)) :
    IntervalIntegrable (fun u => (((x-u)^(g-1)*u^(-1/2:ℝ):ℝ):ℂ)*F u) volume 0 x := by
  -- Only the compact multiplier is continuous at the endpoints; the two singular powers remain in the beta weight.
  let G : ℝ → ℂ := fun u => (((x-u)^(g-1)*u^(-1/2:ℝ):ℝ):ℂ)*F u
  have hC : ContinuousOn (fun r : ℝ => F (x*r)) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    apply hF.comp (continuous_const.mul continuous_id).continuousOn
    intro r hr
    change x*r∈Icc (0:ℝ) x
    exact ⟨mul_nonneg hx.le hr.1,by nlinarith [hr.2]⟩
  have hW := beta_weight_integrable (c := (1/2:ℝ)) (d := g) (by norm_num) hg
  norm_num at hW
  have hB := (hW.mul_continuousOn hC).const_mul
    (((x^(g-1/2):ℝ):ℂ)/(x:ℂ))
  have hcomp : IntervalIntegrable (fun r : ℝ => G (x*r)) volume 0 1 := by
    apply (intervalIntegrable_congr_uIoo (f := fun r : ℝ =>
      (((x^(g-1/2):ℝ):ℂ)/(x:ℂ))*((jacobi.Jacobi.weight (-(1/2)) (g-1) r:ℂ)*F (x*r))) ?_).mp hB
    intro r hr
    rw [uIoo_of_lt (by norm_num : (0:ℝ)<1)] at hr
    have hw := congrArg Complex.ofReal (abel_weight_scaling g hx hr)
    dsimp only
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hx.ne')).mpr
    dsimp [G]
    push_cast at hw ⊢
    simp only [neg_div] at hw ⊢
    linear_combination -F (x*r)*hw
  apply (IntervalIntegrable.comp_mul_left_iff (f := G) (a := 0) (b := x) hx.ne').mp
  simpa only [zero_div,div_self hx.ne'] using hcomp

/-- The literal Mehler--Dirichlet angular integrand is genuinely integrable for every complex frequency and every positive gamma.
Use: justifies splitting its symmetric interval and the original sine integral, and supplies the integrability premise in negative-energy comparisons.
Article: jacobi, Lemma C.1.
Source: beta integrability and the monotone cosine substitution.
Proof: the actual Gauss factor is continuous on the full compact
coordinate interval inside its convergence disk. Transport the genuine
Abel integrability through the actual nonnegative cosine Jacobian and
use the exact mehler_pullback equality away from null endpoints. -/
theorem mehler_integrable {g theta : ℝ} (hg : 0<g) (htheta : theta∈Ioo (0:ℝ) Real.pi)
    (lam : ℂ) :
    IntervalIntegrable (fun v : ℝ => (((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*
      Complex.cos (lam*(v:ℂ))) volume 0 theta := by
  -- The only endpoint regularity required of the hypergeometric factor is ordinary continuity inside its convergence disk.
  let x := angularCoordinate theta
  let H : ℝ → ℂ := fun u =>
    ordinaryHypergeometric ((1/2:ℂ)-lam) ((1/2:ℂ)+lam) (1/2:ℂ) (u:ℂ)
  let G : ℝ → ℂ := fun u => (((x-u)^(g-1)*u^(-1/2:ℝ):ℝ):ℂ)*H u
  have hx : x∈Ioo (0:ℝ) 1 :=
    ⟨angularCoordinate_pos htheta,(angularCoordinate_mem ⟨htheta.1.le,htheta.2⟩).2⟩
  have hG : IntervalIntegrable G volume 0 x := by
    apply abel_integrable hg hx.1
    intro u hu
    have hn : ‖(u:ℂ)‖<1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1]
      exact hu.2.trans_lt hx.2
    exact ((analytic hn).continuousAt.comp continuous_ofReal.continuousAt).continuousWithinAt
  have hsub := intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    (a := 0) (b := theta) (f := angularCoordinate) (f' := fun v => Real.sin v/2) (g := G)
      (by unfold angularCoordinate; fun_prop)
      (fun v _ => angularCoordinate_hasDerivAt v)
      (fun v hv => by
        have hv' : v∈Ioo (0:ℝ) theta := by
          simpa only [min_eq_left htheta.1.le,max_eq_right htheta.1.le] using hv
        exact (div_pos (Real.sin_pos_of_pos_of_lt_pi hv'.1 (hv'.2.trans htheta.2)) (by norm_num)).le)
  simp only [angularCoordinate_properties.1,Function.comp_apply,Complex.real_smul] at hsub
  have hJ := (hsub.mpr hG).const_mul (((2:ℝ)^(g-1):ℝ):ℂ)
  apply (intervalIntegrable_congr_uIoo ?_).mp hJ
  intro v hv
  rw [uIoo_of_lt htheta.1] at hv
  simpa only [G,H,x,mul_assoc] using (mehler_pullback g htheta lam hv).symm

end
end jacobi.Reference.Hypergeometric
