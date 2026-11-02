import jacobi.Elliptic.NormalizedEquation

/-!
Article: jacobi, Theorem D.5.
The clipped semilinear optimizer equation has its exact conserved energy,
including at the free boundary. The actual density energy gives integrability
of y_+³, while the Green H1 energy controls y-sigma and its slope. Therefore
the constant of integration is proved zero on the infinite line.
Source: the autonomous ODE first integral and integrability of a constant on R.
Use: derives integrability of y_+³ from the original finite-energy density.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The actual Euler-density energy has its exact normalized positive-cube integrand.
Use: derives integrability of y_+³ from the original finite-energy density.
Article: jacobi, Theorem D.5.
Proof: the positive-part square has square root (2/3)*a*y_+; cubing that root evaluates the 3/2 power exactly. -/
theorem eulerDensity_energy (m : Density) {μ : ℝ} (hμ : 0<μ) (l x : ℝ) :
    (eulerDensity m μ l x)^(3/2:ℝ)=
      (8/27:ℝ)*(eulerScale μ)^3*(max (eulerState m μ l x) 0)^3 := by
  -- Both amplitude and positive-part factors are nonnegative, fixing the square-root branch.
  have ha := eulerScale_pos hμ
  rw [eulerDensity_normalized m hμ]
  have he : (4/9:ℝ)*(eulerScale μ)^2*(max (eulerState m μ l x) 0)^2=
      ((2/3:ℝ)*eulerScale μ*max (eulerState m μ l x) 0)^2 := by ring
  rw [he,Real.rpow_div_two_eq_sqrt 3 (sq_nonneg _),Real.rpow_ofNat,
    Real.sqrt_sq (by positivity)]
  ring

/-- The positive cube of the actual normalized Euler state is integrable.
Use: forces its conserved first-integral constant to vanish without an assumed endpoint derivative limit.
Article: jacobi, Theorem D.5.
Proof: the actual density equals its Euler representative a.e.; its energy
integrand is a strictly positive constant times y_+³. -/
theorem eulerState_positiveCube_integrable (m : Density) {μ : ℝ} (hμ : 0<μ) (l : ℝ)
    (he : m.value=ᵐ[volume] eulerDensity m μ l) :
    Integrable (fun x => (max (eulerState m μ l x) 0)^3) := by
  -- Integrability is transferred from the original actual objective, not assumed for the ODE profile.
  have hi : Integrable (fun x => (eulerDensity m μ l x)^(3/2:ℝ)) :=
    m.energy_integrable.congr (he.fun_comp (fun r : ℝ => r^(3/2:ℝ)))
  simp_rw [eulerDensity_energy m hμ] at hi
  have hc : (8/27:ℝ)*(eulerScale μ)^3≠0 := ne_of_gt (by have h := eulerScale_pos hμ; positivity)
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp hi

/-- Every actual finite-energy clipped semilinear solution has the exact zero first integral.
Use: the optimizer's turning height and elliptic quadrature follow from this identity.
Article: jacobi, Theorem D.5.
Proof: differentiate d²-4*(y-sigma)²+4*y_+³, using the proved derivative
at the clipping boundary. The result is constant and integrable, so its
constant value is zero on the infinite Lebesgue line. -/
theorem clipped_first_integral {f d : ℝ → ℝ} (σ : ℝ)
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d (4*(f x-σ)-6*(max (f x) 0)^2) x)
    (hf2 : Integrable (fun x => (f x-σ)^2)) (hd2 : Integrable (fun x => d x^2))
    (hf3 : Integrable (fun x => (max (f x) 0)^3)) (x : ℝ) :
    d x^2=4*((f x-σ)^2-(max (f x) 0)^3) := by
  -- Conservation holds at every point, including where f crosses zero.
  let W (y : ℝ) := d y^2-4*(f y-σ)^2+4*(max (f y) 0)^3
  have hW (y : ℝ) : HasDerivAt W 0 y := by
    convert (((hd y).pow 2).sub ((((hf y).sub_const σ).pow 2).const_mul 4)).add
      (((positiveCube_hasDerivAt (f y)).comp y (hf y)).const_mul 4) using 1
    · rfl
    · ring
  have hconst (y : ℝ) : W y=W 0 := is_const_of_deriv_eq_zero
    (fun z => (hW z).differentiableAt) (fun z => (hW z).deriv) y 0
  have hi : Integrable W := (hd2.sub (hf2.const_mul 4)).add (hf3.const_mul 4)
  have hc : Integrable (fun _ : ℝ => W 0) := hi.congr (Eventually.of_forall hconst)
  have hz : W 0=0 := by simpa only [integrable_const_iff,isFiniteMeasure_iff,
    Real.volume_univ,lt_self_iff_false,or_false] using hc
  have hx : W x=0 := (hconst x).trans hz
  dsimp only [W] at hx
  linarith

/-- The original actual second-moment Euler optimizer has the printed exact first integral.
Use: the remaining elliptic quadratures use this fully discharged identity for an actual attained minimizer.
Article: jacobi, Theorem D.5.
Proof: apply the generic conserved-energy theorem to the genuine normalized
state, using its proved classical equation and all three actual integrability bounds. -/
theorem eulerState_first_integral (m : Density) {μ : ℝ} (hμ : 0<μ) (l : ℝ)
    (he : m.value=ᵐ[volume] eulerDensity m μ l) (x : ℝ) :
    (eulerSlope m μ x)^2=4*((eulerState m μ l x-eulerShift μ l)^2-
      (max (eulerState m μ l x) 0)^3) :=
  clipped_first_integral (eulerShift μ l) (eulerState_hasDerivAt m μ l)
    (eulerState_equation m hμ l he) (eulerState_integrable m μ l).1
    (eulerState_integrable m μ l).2 (eulerState_positiveCube_integrable m hμ l he) x

end
end jacobi.Elliptic
