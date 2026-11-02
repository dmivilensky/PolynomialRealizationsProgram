import jacobi.Reference.SingularIntegral

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the trigonometric product identity and linear change of variables.
Use: sine_integrable and sine_integral_angular prove convergence and the exact change of variables for the same original integral.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory _root_.Complex
open Hypergeometric
set_option backward.isDefEq.respectTransparency false

/-- The literal integrand in the article's defining beta representation, before its outside normalizing factor.
Use: sine_integrable and sine_integral_angular prove convergence and the exact change of variables for the same original integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def sineIntegrand (g t : ℝ) (omega : ℂ) (s : ℝ) : ℂ :=
  ((((Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2)^(g-1)):ℝ):ℂ)*
    Complex.cos (((t-2*s:ℝ):ℂ)*omega)

/-- The original sine product is exactly the cosine difference in the true angular change of variables.
Use: sine_integrand_angular transports the actual singular real power, rather than replacing its kernel by an asymptotic approximation.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the classical product-to-sum formula.
Proof: subtract the exact cosine addition and subtraction identities. -/
theorem sine_product_angular (t s : ℝ) :
    Real.cos (Real.pi*t-2*Real.pi*s)-Real.cos (Real.pi*t)=
      2*(Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))) := by
  rw [show Real.pi*t-2*Real.pi*s=Real.pi*(t-s)-Real.pi*s by ring,
    show Real.pi*t=Real.pi*(t-s)+Real.pi*s by ring,Real.cos_sub,Real.cos_add]
  ring

/-- The literal sine integrand has the exact angular expression with its genuine positive-base scaling factor.
Use: proves both convergence and sine_integral_angular for the original article integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: use the exact sine product identity, factor the positive constant
2*pi^2 out of the real power, and identify the actual complex cosine
arguments by field arithmetic. -/
theorem sine_integrand_angular (g : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (omega : ℂ) {s : ℝ} (hs : s∈Icc (0:ℝ) t) :
    sineIntegrand g t omega s=
      ((((2*Real.pi^2)^(1-g)):ℝ):ℂ)*
        ((((Real.cos (Real.pi*t-2*Real.pi*s)-Real.cos (Real.pi*t))^(g-1)):ℝ):ℂ)*
          Complex.cos ((omega/(Real.pi:ℂ))*((Real.pi*t-2*Real.pi*s:ℝ):ℂ)) := by
  -- The sine factors are nonnegative over the entire original integration interval.
  have hsin (r : ℝ) (hr : r∈Icc (0:ℝ) t) : 0≤Real.sin (Real.pi*r) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨mul_nonneg Real.pi_pos.le hr.1,by nlinarith [hr.2,ht.2,Real.pi_pos]⟩
  have hp : 0≤Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s)) :=
    mul_nonneg (hsin s hs) (hsin (t-s) ⟨sub_nonneg.mpr hs.2,by linarith [hs.1]⟩)
  have hc : 0≤Real.cos (Real.pi*t-2*Real.pi*s)-Real.cos (Real.pi*t) := by
    rw [sine_product_angular]; positivity
  have he : Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2=
      (Real.cos (Real.pi*t-2*Real.pi*s)-Real.cos (Real.pi*t))/(2*Real.pi^2) := by
    rw [sine_product_angular]; ring
  have hscale : ((Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2)^(g-1):ℝ)=
      (2*Real.pi^2)^(1-g)*(Real.cos (Real.pi*t-2*Real.pi*s)-Real.cos (Real.pi*t))^(g-1) := by
    rw [he,Real.div_rpow hc (by positivity)]
    rw [show (1-g:ℝ)= -(g-1) by ring,Real.rpow_neg (by positivity)]
    ring
  have harg : ((t-2*s:ℝ):ℂ)*omega=
      (omega/(Real.pi:ℂ))*((Real.pi*t-2*Real.pi*s:ℝ):ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [sineIntegrand,hscale,harg,Complex.ofReal_mul,mul_assoc]

/-- A genuinely integrable even function has twice its positive-half integral on the symmetric interval.
Use: folds the original transformed sine integral to the physical Mehler--Dirichlet interval in sine_integral_angular.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: reflection invariance of the Lebesgue integral.
Proof: reflect the genuine positive-half integrability and integral, then add the two adjacent interval integrals. -/
theorem even_integral {F : ℝ → ℂ} {theta : ℝ} (hF : Function.Even F)
    (hi : IntervalIntegrable F volume 0 theta) :
    (∫ v in -theta..theta,F v)=2*(∫ v in (0:ℝ)..theta,F v) := by
  have hfun : (fun v => F (-v))=F := funext hF
  have hn : IntervalIntegrable F volume (-theta) 0 := by
    simpa only [zero_sub,sub_zero,hfun] using (hi.comp_sub_left 0).symm
  have he : (∫ v in -theta..(0:ℝ),F v)=∫ v in (0:ℝ)..theta,F v := by
    simpa only [hfun,neg_zero] using (intervalIntegral.integral_comp_neg (f := F) (a := 0) (b := theta)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hn hi,he]
  ring

/-- The genuine angular kernel is even and integrable on its full symmetric change-of-variables interval.
Use: supplies the actual convergence premise for sine_integrable and for the folding step in sine_integral_angular.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: reflect the proved positive-half Mehler integrability and join the adjacent intervals. -/
theorem symmetric_mehler_integrable {g theta : ℝ} (hg : 0<g)
    (htheta : theta∈Ioo (0:ℝ) Real.pi) (lam : ℂ) :
    IntervalIntegrable (fun v : ℝ => (((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*
      Complex.cos (lam*(v:ℂ))) volume (-theta) theta := by
  let M : ℝ → ℂ := fun v => (((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*Complex.cos (lam*(v:ℂ))
  have he : Function.Even M := by intro v; simp [M]
  have hi : IntervalIntegrable M volume 0 theta := mehler_integrable hg htheta lam
  have hfun : (fun v => M (-v))=M := funext he
  have hn : IntervalIntegrable M volume (-theta) 0 := by
    simpa only [zero_sub,sub_zero,hfun] using (hi.comp_sub_left 0).symm
  exact hn.trans hi

/-- The literal defining sine integral is genuinely convergent for every complex frequency in the full article parameter range.
Use: negative-energy positivity and domination estimates apply to the actual reference integral with all integrability premises discharged.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: transport the proved symmetric Mehler integrability through the
actual affine substitution; sine_integrand_angular identifies the
integrands on the original open interval, so singular null endpoints
require no extra continuity assumption. -/
theorem sine_integrable {g t : ℝ} (hg : 0<g) (ht : t∈Ioo (0:ℝ) 1) (omega : ℂ) :
    IntervalIntegrable (sineIntegrand g t omega) volume 0 t := by
  -- This is a change of variables for genuinely integrable functions, not an inference from a totalized integral value.
  let theta := Real.pi*t
  let M : ℝ → ℂ := fun v => (((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*
    Complex.cos ((omega/(Real.pi:ℂ))*(v:ℂ))
  have htheta : theta∈Ioo (0:ℝ) Real.pi :=
    ⟨mul_pos Real.pi_pos ht.1,by dsimp [theta]; nlinarith [Real.pi_pos,ht.2]⟩
  have hi := symmetric_mehler_integrable hg htheta (omega/(Real.pi:ℂ))
  have hlin := ((hi.comp_sub_left theta).symm).comp_mul_left (c := 2*Real.pi)
  have hlin' : IntervalIntegrable (fun s : ℝ => M (theta-2*Real.pi*s)) volume 0 t := by
    convert! hlin using 1 <;> dsimp [theta] <;> field_simp [Real.pi_ne_zero] <;> ring
  have hscaled := hlin'.const_mul ((((2*Real.pi^2)^(1-g)):ℝ):ℂ)
  apply (intervalIntegrable_congr_uIoo ?_).mp hscaled
  intro s hs
  rw [uIoo_of_lt ht.1] at hs
  simpa only [M,theta,mul_assoc] using (sine_integrand_angular g ht omega ⟨hs.1.le,hs.2.le⟩).symm

/-- The literal original sine integral is exactly its angular Mehler--Dirichlet integral with the full scale, for every complex frequency.
Use: together with mehler_reference_identity this proves the defining beta-integral equality for the existing wave and solution.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: substitute v=pi*t-2*pi*s on the genuine integral, fold its even
angular integrand using established integrability, and cancel the exact
linear Jacobian 2*pi against the two equal halves. -/
theorem sine_integral_angular {g t : ℝ} (hg : 0<g) (ht : t∈Ioo (0:ℝ) 1) (omega : ℂ) :
    (∫ s in (0:ℝ)..t,sineIntegrand g t omega s)=
      (((2*Real.pi^2)^(1-g)/Real.pi:ℝ):ℂ)*
        (∫ v in (0:ℝ)..Real.pi*t,(((Real.cos v-Real.cos (Real.pi*t))^(g-1):ℝ):ℂ)*
          Complex.cos ((omega/(Real.pi:ℂ))*(v:ℂ))) := by
  -- The affine substitution and the folding identity act on the same literal integrand.
  let theta := Real.pi*t
  let M : ℝ → ℂ := fun v => (((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*
    Complex.cos ((omega/(Real.pi:ℂ))*(v:ℂ))
  have htheta : theta∈Ioo (0:ℝ) Real.pi :=
    ⟨mul_pos Real.pi_pos ht.1,by dsimp [theta]; nlinarith [Real.pi_pos,ht.2]⟩
  have heven : Function.Even M := by intro v; simp [M]
  have he := even_integral heven (mehler_integrable hg htheta (omega/(Real.pi:ℂ)))
  have hlin := intervalIntegral.integral_comp_sub_mul (f := M) (a := 0) (b := t)
    (c := 2*Real.pi) (by positivity) theta
  rw [show theta-2*Real.pi*t= -theta by dsimp [theta]; ring] at hlin
  simp only [mul_zero,sub_zero,Complex.real_smul,he] at hlin
  calc
    _ = ((((2*Real.pi^2)^(1-g)):ℝ):ℂ)*(∫ s in (0:ℝ)..t,M (theta-2*Real.pi*s)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
      intro s hs
      simpa only [M,theta,mul_assoc] using sine_integrand_angular g ht omega ⟨hs.1.le,hs.2.le⟩
    _ = _ := by
      rw [hlin]
      dsimp only [M,theta]
      push_cast
      simp only [div_mul_eq_mul_div]
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end
end jacobi.Reference
