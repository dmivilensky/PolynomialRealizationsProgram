import jacobi.Keller.Calibration
import jacobi.Young.SemilinearUniqueness

/-!
Article: jacobi, Theorem D.6.
The free normalized optimizing ground state obeys u'²=u²-u⁶ and
u''=u-3u⁵. Consequently its positive reciprocal square solves q''=4q
with q(0)=1 and q'(0)=0. The already proved global initial-value uniqueness
identifies q=cosh(2x), yielding the literal stated sech-squared attainer.
Source: Keller's equality profile, proved by the shared Picard--Lindelof uniqueness theorem.
Use: identifies the genuine attained density with the classical explicit Keller extremal.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
open chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false
variable {m : Density} {ell M : ℝ}

/-- The actual free Keller ground square is exactly sech(2x).
Use: identifies the genuine attained density with the classical explicit Keller extremal.
Article: jacobi, Theorem D.6.
Proof: the positive reciprocal ground square has the linear equation
q''=4q by the actual first integral and Euler equation. It has initial
data (1,0), so the reused global ODE uniqueness theorem gives q=cosh(2x). -/
theorem Profile.free_ground_square (p : Profile m ell M) (hell : 0<ell)
    (hc : p.shape=1) (x : ℝ) : H1.rep p.u x^2= jacobi.Young.sech (2*x) := by
  -- Reciprocal square removes the nonlinear term using the actual zero first integral.
  let u := H1.rep p.u
  let f (y : ℝ) := (u y^2)⁻¹
  let d (y : ℝ) := -2*p.d y/u y^3
  have hedge : p.edge=0 := p.shape_eq_one_iff.mp hc
  have hb : p.b=3*ell/2 := by simpa only [hc,one_pow,mul_one] using p.amplitude hell
  have hi (y : ℝ) : p.d y^2=u y^2-u y^6 := by
    have hh := p.first_integral hell y
    rw [hedge,sub_zero,max_eq_left (sq_nonneg _),hb] at hh
    have hcoef : 2*(3*ell/2)/(3*ell)=1 := by field_simp
    simpa only [hcoef,one_mul,← pow_mul] using hh
  have hode (y : ℝ) : HasDerivAt p.d (u y-3*u y^5) y := by
    have hh := p.equation y
    rw [hedge,sub_zero,max_eq_left (sq_nonneg _),hb] at hh
    convert! hh using 1
    dsimp only [u]
    field_simp [hell.ne']
  have hf (y : ℝ) : HasDerivAt f (d y) y := by
    convert ((p.derivative y).pow 2).inv (sq_pos_of_pos (p.positive y)).ne' using 1
    dsimp only [f,d,u,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    field_simp [(p.positive y).ne']
  have hd (y : ℝ) : HasDerivAt d (4*f y-(0:ℝ)*f y^2) y := by
    convert ((hode y).const_mul (-2:ℝ)).div ((p.derivative y).pow 3) (pow_pos (p.positive y) 3).ne' using 1
    dsimp only [f,u,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,zero_mul,sub_zero]
    field_simp [(p.positive y).ne']
    have hi' := hi y
    dsimp only [u] at hi'
    nlinarith [hi']
  have hg (y : ℝ) : HasDerivAt (fun t : ℝ => cosh (2*t)) (2*sinh (2*y)) y := by
    convert (hasDerivAt_cosh (2*y)).comp y ((hasDerivAt_id y).const_mul (2:ℝ)) using 1
    · rfl
    · ring
  have he (y : ℝ) : HasDerivAt (fun t : ℝ => 2*sinh (2*t))
      (4*cosh (2*y)-(0:ℝ)*(cosh (2*y))^2) y := by
    convert ((hasDerivAt_sinh (2*y)).comp y ((hasDerivAt_id y).const_mul (2:ℝ))).const_mul (2:ℝ) using 1
    · rfl
    · ring
  have h0 : f 0=cosh (2*0) := by simp [f,u,p.center]
  have h1 : d 0=2*sinh (2*0) := by simp [d,u,p.center,p.center_slope]
  have hh := (jacobi.Young.semilinear_unique 0 0 hf hd hg he h0 h1).1
  change u x^2=(cosh (2*x))⁻¹
  rw [← congrFun hh x]
  exact (inv_inv _).symm

/-- The original actual free-mass optimizer is the literal classical Keller density almost everywhere.
Use: provides the explicit attaining density, with its exact amplitude and spatial scale.
Article: jacobi, Theorem D.6.
Proof: its cutoff is zero, its amplitude is 3*ell/2, and the proved actual
ground square equals sech(2x); substitute in the original a.e. Euler identity. -/
theorem Profile.free_density (p : Profile m ell M) (hell : 0<ell) (hc : p.shape=1) :
    m.value=ᵐ[volume] fun x => (3*ell/2)*(jacobi.Young.sech (2*x))^2 := by
  filter_upwards [p.density] with x hx
  rw [hx,p.shape_eq_one_iff.mp hc,sub_zero,max_eq_left (sq_nonneg _),p.amplitude hell,
    hc,one_pow,mul_one,p.free_ground_square hell hc]

/-- The free Keller infimum is attained by the printed sech-squared density with the exact spectral constraint.
Use: closes the source's classical attaining-profile assertion alongside the exact minimum formula.
Article: jacobi, Theorem D.6.
Proof: the complete actual free calibration supplies an attainer and its
shape-one ground profile; the proved literal-profile identity identifies that same attainer. -/
theorem free_attainer {ell M : ℝ} (hell : 0<ell) (hsub : ell<M) (hregime : 3*ell/2≤M) :
    ∃ m : Density,m.value=ᵐ[volume] (fun x => (3*ell/2)*(jacobi.Young.sech (2*x))^2) ∧
      m.mass=3*ell/2 ∧ observe m .top=ell ∧ m.energy=freeValue ell ∧ m.cost=Kel ell M := by
  obtain ⟨_hvalue,m,_hs,hm,hG,hE,hcost,p,hc⟩ := free_calibration hell hsub hregime
  exact ⟨m,p.free_density hell hc,hm,hG,hE,hcost⟩

end
end jacobi.Keller
