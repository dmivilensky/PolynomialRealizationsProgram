import jacobi.Reference.BetaConvolution
import jacobi.Reference.MehlerCoordinate

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The actual angular integral is changed to the original beta convolution.
The monotone substitution theorem handles the genuine singular endpoint
powers. All powers are combined at positive interior bases, so no
totalized endpoint arithmetic is used to infer an integral identity.
Source: Euler's fractional integral and the Mehler--Dirichlet substitution.
Use: proves abel_hypergeometric under the true substitution u=x*r.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual Abel weight scales to the original beta weight with its exact power of the interval length.
Use: proves abel_hypergeometric under the true substitution u=x*r.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: factor x from both positive endpoint distances and combine the
three genuine positive-base powers x^1*x^(gamma-1)*x^(-1/2). -/
theorem abel_weight_scaling (g : ℝ) {x r : ℝ} (hx : 0<x) (hr : r∈Ioo (0:ℝ) 1) :
    x*(x-x*r)^(g-1)*(x*r)^(-1/2:ℝ)=
      x^(g-1/2)* jacobi.Jacobi.weight (-1/2) (g-1) r := by
  -- Each power identity is applied at a genuinely positive base inside the original interval.
  rw [show x-x*r=x*(1-r) by ring,Real.mul_rpow hx.le (sub_nonneg.mpr hr.2.le),
    Real.mul_rpow hx.le hr.1.le]
  have hp : x*x^(g-1)*x^(-1/2:ℝ)=x^(g-1/2) := by
    calc
      _ = x^(1+(g-1)+(-1/2:ℝ)) := by rw [Real.rpow_add hx,Real.rpow_add hx,Real.rpow_one]
      _ = _ := by congr 1; ring
  unfold jacobi.Jacobi.weight
  linear_combination (1-r)^(g-1)*r^(-1/2:ℝ)*hp

/-- The actual Abel integral of the Gauss function is exactly its beta-convolved raised-parameter function, including its original interval scale.
Use: evaluates the angular Mehler--Dirichlet integral after the monotone cosine substitution.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: Euler's hypergeometric fractional-integral identity, proved here for genuine interval integrals.
Proof: substitute u=x*r by the community linear change-of-variables
theorem. The exact positive-base scaling gives the original beta
weight on [0,1]. Apply the proved dominated beta_convolution identity. -/
theorem abel_hypergeometric (a b : ℂ) {g x : ℝ} (hg : 0<g) (hx : x∈Ioo (0:ℝ) 1) :
    (∫ u in (0:ℝ)..x,(((x-u)^(g-1)*u^(-1/2:ℝ):ℝ):ℂ)*
      ordinaryHypergeometric a b (1/2:ℂ) (u:ℂ))=
        ((x^(g-1/2):ℝ):ℂ)*
          (Complex.Gamma (1/2:ℂ)*Complex.Gamma (g:ℂ)/Complex.Gamma ((1/2:ℂ)+(g:ℂ)))*
            ordinaryHypergeometric a b ((1/2:ℂ)+(g:ℂ)) (x:ℂ) := by
  -- The original singular integral is transported without imposing endpoint continuity.
  let G : ℝ → ℂ := fun u => (((x-u)^(g-1)*u^(-1/2:ℝ):ℝ):ℂ)*
    ordinaryHypergeometric a b (1/2:ℂ) (u:ℂ)
  have hsub := intervalIntegral.smul_integral_comp_mul_left (f := G) (a := 0) (b := 1) x
  simp only [mul_zero,mul_one,Complex.real_smul] at hsub
  change (∫ u in (0:ℝ)..x,G u)=_
  rw [← hsub,← intervalIntegral.integral_const_mul]
  have he : (∫ r in (0:ℝ)..1,(x:ℂ)*G (x*r))=
      ((x^(g-1/2):ℝ):ℂ)*(∫ r in (0:ℝ)..1,
        (jacobi.Jacobi.weight (-1/2) (g-1) r:ℂ)*
          ordinaryHypergeometric a b (1/2:ℂ) ((x:ℂ)*(r:ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro r hr
    dsimp [G]
    have hw := congrArg Complex.ofReal (abel_weight_scaling g hx.1 hr)
    push_cast at hw
    push_cast
    linear_combination ordinaryHypergeometric a b (1/2:ℂ) ((x:ℂ)*(r:ℂ))*hw
  rw [he]
  have hn : ‖(x:ℂ)‖<1 := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1]; exact hx.2
  have hb := beta_convolution a b (c := (1/2:ℝ)) (d := g) (by norm_num) hg hn
  norm_num at hb
  simpa only [mul_assoc,neg_div] using congrArg (fun z : ℂ => ((x^(g-1/2):ℝ):ℂ)*z) hb

/-- The original angular integrand is exactly the beta-coordinate pullback, with the genuine derivative factor.
Use: proves both mehler_beta_identity and convergence of its actual singular integral in SingularIntegral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the classical cosine substitution in Euler's fractional integral.
Proof: Euler's cosine representation cancels the square-root Jacobian;
positive-base real powers split the exact factor of two. -/
theorem mehler_pullback (g : ℝ) {theta : ℝ} (htheta : theta∈Ioo (0:ℝ) Real.pi)
    (lam : ℂ) {v : ℝ} (hv : v∈Ioo (0:ℝ) theta) :
    (((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*Complex.cos (lam*(v:ℂ))=
      (((2:ℝ)^(g-1):ℝ):ℂ)*((Real.sin v/2:ℝ):ℂ)*
        ((((angularCoordinate theta-angularCoordinate v)^(g-1)*(angularCoordinate v)^(-1/2:ℝ)):ℝ):ℂ)*
          ordinaryHypergeometric ((1/2:ℂ)-lam) ((1/2:ℂ)+lam) (1/2:ℂ) (angularCoordinate v:ℂ) := by
  -- The singular endpoint bases are positive at every point where an algebraic cancellation is made.
  have hvpi : v∈Ioo (0:ℝ) Real.pi := ⟨hv.1,hv.2.trans htheta.2⟩
  have hdiff : 0≤angularCoordinate theta-angularCoordinate v := by
    have hh := angularCoordinate_properties.2 ⟨hv.1.le,hvpi.2.le⟩ ⟨htheta.1.le,htheta.2.le⟩ hv.2
    exact (sub_pos.mpr hh).le
  have hcos : Real.cos v-Real.cos theta=2*(angularCoordinate theta-angularCoordinate v) := by
    dsimp [angularCoordinate]; ring
  rw [cosine_beta_representation lam ⟨hv.1.le,hvpi.2⟩,hcos,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2) hdiff]
  have hj := congrArg Complex.ofReal (angularCoordinate_jacobian hvpi)
  push_cast at hj ⊢
  linear_combination -(((2:ℝ)^(g-1):ℝ):ℂ)*
    (((angularCoordinate theta-angularCoordinate v)^(g-1):ℝ):ℂ)*
      ordinaryHypergeometric ((1/2:ℂ)-lam) ((1/2:ℂ)+lam) (1/2:ℂ) (angularCoordinate v:ℂ)*hj

/-- The literal Mehler--Dirichlet angular integral is the exact raised-parameter Gauss expression with its original beta normalization.
Use: Euler's transformation and Gamma duplication identify this genuine integral with the article's displayed reference solution.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: Mehler--Dirichlet integral, DLMF 14.12.1, proved here through the actual beta convolution.
Proof: the monotone coordinate u=(1-cos(v))/2 has derivative sin(v)/2.
The proved weighted cosine identity cancels its square-root Jacobian.
The literal angular power becomes 2^(gamma-1)*(x-u)^(gamma-1).
Apply abel_hypergeometric to the actual remaining integral. -/
theorem mehler_beta_identity {g theta : ℝ} (hg : 0<g) (htheta : theta∈Ioo (0:ℝ) Real.pi)
    (lam : ℂ) :
    (∫ v in (0:ℝ)..theta,(((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*Complex.cos (lam*(v:ℂ)))=
      (((2:ℝ)^(g-1)*(angularCoordinate theta)^(g-1/2):ℝ):ℂ)*
        (Complex.Gamma (1/2:ℂ)*Complex.Gamma (g:ℂ)/Complex.Gamma ((1/2:ℂ)+(g:ℂ)))*
          ordinaryHypergeometric ((1/2:ℂ)-lam) ((1/2:ℂ)+lam)
            ((1/2:ℂ)+(g:ℂ)) (angularCoordinate theta:ℂ) := by
  -- The true angular substitution is monotone on precisely the original physical interval.
  let x := angularCoordinate theta
  let G : ℝ → ℂ := fun u => (((x-u)^(g-1)*u^(-1/2:ℝ):ℝ):ℂ)*
    ordinaryHypergeometric ((1/2:ℂ)-lam) ((1/2:ℂ)+lam) (1/2:ℂ) (u:ℂ)
  have hx : x∈Ioo (0:ℝ) 1 :=
    ⟨angularCoordinate_pos htheta,(angularCoordinate_mem ⟨htheta.1.le,htheta.2⟩).2⟩
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := 0) (b := theta) (f := angularCoordinate) (f' := fun v => Real.sin v/2) (g := G)
      (by unfold angularCoordinate; fun_prop)
      (fun v _ => angularCoordinate_hasDerivAt v)
      (fun v hv => by
        have hv' : v∈Ioo (0:ℝ) theta := by simpa only [min_eq_left htheta.1.le,max_eq_right htheta.1.le] using hv
        exact (div_pos (Real.sin_pos_of_pos_of_lt_pi hv'.1 (hv'.2.trans htheta.2)) (by norm_num)).le)
  simp only [angularCoordinate_properties.1,Function.comp_apply,Complex.real_smul] at hsub
  have he : (∫ v in (0:ℝ)..theta,(((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*Complex.cos (lam*(v:ℂ)))=
      (((2:ℝ)^(g-1):ℝ):ℂ)*(∫ u in (0:ℝ)..x,G u) := by
    rw [← hsub,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le htheta.1.le
    intro v hv
    dsimp only
    simpa only [G,x,mul_assoc] using mehler_pullback g htheta lam hv
  rw [he,abel_hypergeometric _ _ hg hx]
  push_cast
  ring

end
end jacobi.Reference.Hypergeometric
