import jacobi.Keller.Coordinate

/-!
Article: jacobi, Theorem D.6.
The positive normalized ground branch supplies an injective change of
variables. Its proved first integral fixes the positive square-root branch
of the derivative; the original Euler density has the printed polynomial
expression in this same coordinate. No quadrature identity is assumed.
Source: the classical chain rule and the one-dimensional Lebesgue Jacobian theorem.
Use: supplies the derivative, with its sign, to the genuine change of variables.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
open chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false
variable {m : Density} {ell M : ℝ}

/-- The actual derivative of the optimizing coordinate on its positive half-line.
Use: supplies the derivative, with its sign, to the genuine change of variables.
Article: jacobi, Theorem D.6.
Proof: differentiate the positive square root and cancel its factor two. -/
theorem Profile.coordinate_derivative (p : Profile m ell M) (hell : 0<ell)
    {x : ℝ} (hx : 0<x) :
    HasDerivAt p.coordinate (-p.shape*H1.rep p.u x*p.d x/p.coordinate x) x := by
  have hp := p.coordinate_pos hell hx
  have ha : 0<p.shape*(1-H1.rep p.u x^2) := sqrt_pos.mp hp
  convert ((((p.derivative x).pow 2).const_sub 1).const_mul p.shape).sqrt ha.ne' using 1
  · rfl
  · dsimp only [Profile.coordinate,Pi.pow_apply]
    field_simp
    ring

/-- The coordinate increases with a strictly positive actual derivative.
Use: selects the positive square-root Jacobian and excludes zero denominators.
Article: jacobi, Theorem D.6.
Proof: the normalized ground state and c are positive, its slope is negative,
and the coordinate is strictly positive away from the center. -/
theorem Profile.coordinate_slope_pos (p : Profile m ell M) (hell : 0<ell)
    {x : ℝ} (hx : 0<x) : 0< -p.shape*H1.rep p.u x*p.d x/p.coordinate x := by
  exact div_pos (mul_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (zero_lt_one.trans_le (p.shape_ge_one hell))) (p.positive x))
    (p.slope_neg x hx)) (p.coordinate_pos hell hx)

/-- The normalized ground slope has the exact Keller polynomial square on the actual half-core.
Use: eliminates the original ODE from the quadrature Jacobian algebra.
Article: jacobi, Theorem D.6.
Proof: substitute b=(3*ell/2)*c³ and c*(u²-v_e)=1-sigma²
into the proved zero first integral, then expand the polynomial. -/
theorem Profile.slope_square (p : Profile m ell M) (hell : 0<ell)
    {x : ℝ} (hx : x∈p.core) :
    p.d x^2=(p.coordinate x^2/p.shape)*(p.shape*A (p.coordinate x)-1) := by
  -- Every cancellation uses the same genuine shape and coordinate of the optimizer.
  have hc : 0<p.shape := zero_lt_one.trans_le (p.shape_ge_one hell)
  have hv := p.coordinate_pos hell hx.1
  have hv1 : p.coordinate x<1 := hx.2
  have hg := p.coordinate_gap hell x
  have hs := p.coordinate_sq hell x
  have he : 0<H1.rep p.u x^2-p.edge := by
    have hh : 0<1-p.coordinate x^2 := by nlinarith
    nlinarith
  have hi := p.first_integral hell x
  rw [max_eq_left he.le,p.amplitude hell] at hi
  have hcoef : 2*((3*ell/2)*p.shape^3)/(3*ell)=p.shape^3 := by field_simp
  rw [hcoef] at hi
  have hcub : p.shape^3*(H1.rep p.u x^2-p.edge)^3=(1-p.coordinate x^2)^3 := by
    rw [← mul_pow,hg]
  rw [hcub] at hi
  unfold A
  rw [hi]
  field_simp [hc.ne']
  nlinarith [hs]

/-- The actual coordinate derivative is the printed positive square-root Jacobian.
Use: proves all Keller integral identities by the genuine Lebesgue substitution formula.
Article: jacobi, Theorem D.6.
Proof: square the actual derivative, use the proved ground slope polynomial,
and recover the positive branch from its proved strict sign. -/
theorem Profile.coordinate_jacobian (p : Profile m ell M) (hell : 0<ell)
    {x : ℝ} (hx : x∈p.core) :
    -p.shape*H1.rep p.u x*p.d x/p.coordinate x=
      sqrt p.shape*sqrt ((1-p.coordinate x^2/p.shape)*(p.shape*A (p.coordinate x)-1)) := by
  -- Positivity of the actual slope also proves positivity of the radicand.
  have hc : 0<p.shape := zero_lt_one.trans_le (p.shape_ge_one hell)
  have hv := p.coordinate_pos hell hx.1
  have hs := p.coordinate_sq hell x
  have hd := p.slope_square hell hx
  let D := -p.shape*H1.rep p.u x*p.d x/p.coordinate x
  let Q := (1-p.coordinate x^2/p.shape)*(p.shape*A (p.coordinate x)-1)
  have hD : 0<D := p.coordinate_slope_pos hell hx.1
  have hu : H1.rep p.u x^2=1-p.coordinate x^2/p.shape := by
    field_simp [hc.ne']
    nlinarith [hs]
  have hsq : D^2=p.shape*Q := by
    calc
      D^2=p.shape^2*H1.rep p.u x^2*p.d x^2/p.coordinate x^2 := by dsimp only [D]; ring
      _=p.shape*Q := by
        rw [hd,hu]
        dsimp only [Q]
        field_simp
  have hQ : 0<Q := by nlinarith [sq_pos_of_pos hD]
  have ht : (sqrt p.shape*sqrt Q)^2=p.shape*Q := by
    rw [mul_pow,sq_sqrt hc.le,sq_sqrt hQ.le]
  exact (sq_eq_sq₀ hD.le (mul_pos (sqrt_pos.mpr hc) (sqrt_pos.mpr hQ)).le).mp (hsq.trans ht.symm)

/-- The literal optimizing density representative, built from the actual ground state.
Use: allows pointwise changes of variables before transferring results to the original density a.e.
Article: jacobi, Theorem D.6.
-/
def Profile.rho (p : Profile m ell M) (x : ℝ) : ℝ := p.b*(max (H1.rep p.u x^2-p.edge) 0)^2

/-- The actual density in the optimizing coordinate has the printed normalized polynomial form.
Use: mass and energy become exactly j_2 and j_3, with the source's constants.
Article: jacobi, Theorem D.6.
Proof: remove the positive-part clipping inside the genuine core, substitute
the proved amplitude, and square c*(u²-v_e)=1-sigma². -/
theorem Profile.rho_core (p : Profile m ell M) (hell : 0<ell) {x : ℝ} (hx : x∈p.core) :
    p.rho x=(3*ell/2)*p.shape*(1-p.coordinate x^2)^2 := by
  -- Inside the actual core the cutoff gap is positive, so clipping disappears before amplitude cancellation.
  have hc : 0<p.shape := zero_lt_one.trans_le (p.shape_ge_one hell)
  have hv := p.coordinate_pos hell hx.1
  have hv1 : p.coordinate x<1 := hx.2
  have hg := p.coordinate_gap hell x
  have he : 0<H1.rep p.u x^2-p.edge := by nlinarith
  unfold Profile.rho
  rw [max_eq_left he.le,p.amplitude hell]
  calc
    _ = (3*ell/2)*p.shape*(p.shape*(H1.rep p.u x^2-p.edge))^2 := by ring
    _ = _ := by rw [hg]

/-- The literal optimizing density vanishes outside its positive half-core on the positive half-line.
Use: the whole-line integral reduces exactly to the domain of the genuine coordinate substitution.
Article: jacobi, Theorem D.6.
Proof: sigma>=1 forces u²-v_e<=0 by the proved coordinate gap. -/
theorem Profile.rho_off_core (p : Profile m ell M) (hell : 0<ell) {x : ℝ}
    (hx : 0<x) (hn : x∉p.core) : p.rho x=0 := by
  have hc : 0<p.shape := zero_lt_one.trans_le (p.shape_ge_one hell)
  have hv : 1≤p.coordinate x := by
    by_contra! hh
    exact hn ⟨hx,hh⟩
  have hg := p.coordinate_gap hell x
  have he : H1.rep p.u x^2-p.edge≤0 := by nlinarith
  simp only [Profile.rho,max_eq_right he,zero_pow (by decide : 2≠0),mul_zero]

/-- Every observable vanishing at zero has the exact whole-line Keller quadrature on the actual optimizer.
Use: computes its original mass, objective energy and root mass with no numerical or profile premises.
Article: jacobi, Theorem D.6.
Proof: the actual coordinate maps its measurable half-core bijectively onto
(0,1). Its proved positive Jacobian cancels the printed square root.
The observable vanishes off the core; evenness doubles the half-line integral. -/
theorem Profile.quadrature (p : Profile m ell M) (hell : 0<ell)
    (F : ℝ → ℝ) (hF : F 0=0) :
    (∫ x,F (p.rho x))=(2/sqrt p.shape)*∫ v in (0:ℝ)..1,
      F ((3*ell/2)*p.shape*(1-v^2)^2)/sqrt ((1-v^2/p.shape)*(p.shape*A v-1)) := by
  -- The Jacobian theorem is applied to the genuine optimizer, not to a proposed inverse profile.
  let g (v : ℝ) := F ((3*ell/2)*p.shape*(1-v^2)^2)/sqrt ((1-v^2/p.shape)*(p.shape*A v-1))
  have hc : 0<p.shape := zero_lt_one.trans_le (p.shape_ge_one hell)
  have hs : 0<sqrt p.shape := sqrt_pos.mpr hc
  have hjac (x : ℝ) (hx : x∈p.core) :
      |-p.shape*H1.rep p.u x*p.d x/p.coordinate x| • g (p.coordinate x)=
        sqrt p.shape*F (p.rho x) := by
    have hpos := p.coordinate_slope_pos hell hx.1
    have hh := p.coordinate_jacobian hell hx
    have hden : 0<sqrt ((1-p.coordinate x^2/p.shape)*(p.shape*A (p.coordinate x)-1)) := by
      exact (mul_pos_iff_of_pos_left hs).mp (hh ▸ hpos)
    rw [abs_of_pos hpos,hh,p.rho_core hell hx]
    dsimp only [g,smul_eq_mul]
    calc
      _ = sqrt p.shape*(sqrt ((1-p.coordinate x^2/p.shape)*(p.shape*A (p.coordinate x)-1))*
        F ((3*ell/2)*p.shape*(1-p.coordinate x^2)^2)/
          sqrt ((1-p.coordinate x^2/p.shape)*(p.shape*A (p.coordinate x)-1))) := by ring
      _ = _ := by rw [mul_div_cancel_left₀ _ hden.ne']
  have hchange := integral_image_eq_integral_abs_deriv_smul p.core_measurable
    (fun x hx => (p.coordinate_derivative hell hx.1).hasDerivWithinAt)
    (p.coordinate_strictMono hell |>.mono (fun _ hx => hx.1)).injOn g
  rw [p.coordinate_image hell] at hchange
  have hr : (∫ x in p.core,|-p.shape*H1.rep p.u x*p.d x/p.coordinate x| • g (p.coordinate x))=
      sqrt p.shape*(∫ x in p.core,F (p.rho x)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun p.core_measurable hjac
  rw [hr] at hchange
  have habs (x : ℝ) : p.rho |x|=p.rho x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · simp only [abs_of_nonpos hx,Profile.rho,p.even]
  have hfull : (∫ x,F (p.rho x))=2*(∫ x in Ioi (0:ℝ),F (p.rho x)) := by
    simpa only [habs] using (integral_comp_abs (f := fun x => F (p.rho x)))
  have hrestrict : (∫ x in Ioi (0:ℝ),F (p.rho x))=∫ x in p.core,F (p.rho x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ hx => hx.1)
    intro x hx
    rw [p.rho_off_core hell hx.1 hx.2,hF]
  rw [hfull,hrestrict]
  have hi : (∫ v in (0:ℝ)..1,g v)=sqrt p.shape*(∫ x in p.core,F (p.rho x)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
    exact hchange
  change _=(2/sqrt p.shape)*∫ v in (0:ℝ)..1,g v
  rw [hi]
  field_simp

end
end jacobi.Keller
