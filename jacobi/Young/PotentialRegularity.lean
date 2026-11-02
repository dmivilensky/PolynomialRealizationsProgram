import jacobi.Young.HolderRigidity

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
The actual exponent-two Green potential is C1 for every L1 density and C2
for continuous densities. Equality in Young supplies a continuous square
representative of the original measurable density; the original potential
then satisfies the classical semilinear equation, with no assumed regularity.
Source: the proved exponent-one Green calculus in chebyshev2, rescaled exactly.
Use: both equality classification and the moment-gradient regularity use this literal C1 potential.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real Filter jacobi.Variational
open chebyshev2.GroundState chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- The actual exponent-two potential has its declared derivative everywhere.
Use: both equality classification and the moment-gradient regularity use this literal C1 potential.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: compose the existing exponent-one derivative with x to 2x and cancel the prefactor one half. -/
theorem potential_hasDerivAt (m : Density) (x : ℝ) :
    HasDerivAt (potential m) (potentialSlope m x) x := by
  convert ((convolution_hasDerivAt (source_integrable m) (2*x)).comp x
    ((hasDerivAt_id x).const_mul 2)).const_mul (1/2 : ℝ) using 1
  · rfl
  · dsimp only [potentialSlope]; ring

/-- The actual Green potential and its actual slope are continuous.
Use: its classical semilinear equation has a continuous right-hand side in the equality case.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: use the pointwise derivative for the potential and the existing continuous convolution slope. -/
theorem potential_continuous (m : Density) : Continuous (potential m) ∧ Continuous (potentialSlope m) :=
  ⟨continuous_iff_continuousAt.mpr (fun x => (potential_hasDerivAt m x).continuousAt),
    (convolutionSlope_continuous (source_integrable m)).comp (continuous_const.mul continuous_id)⟩

/-- A continuous density gives the actual classical second Green derivative.
Use: the elliptic and equality ODEs follow from the integral operator rather than an assumed weak solution.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the existing locally absolutely continuous slope has a continuous a.e.
derivative, hence that derivative holds everywhere; rescale the old Green equation. -/
theorem potential_second_derivative (m : Density) (hm : Continuous m.value) (x : ℝ) :
    HasDerivAt (potentialSlope m) (4*potential m x-4*m.value x) x := by
  -- Upgrade the old a.e. derivative before composing, so no null-set substitution is tacit.
  have hc : Continuous (source m) := hm.comp (continuous_id.div_const 2)
  have hd (y : ℝ) := locallyAC_hasDerivAt_of_continuous
    (convolutionSlope_locallyAC (source_integrable m))
    (convolution_second_derivative_ae (source_integrable m))
    ((H1.continuous_rep _).sub (hc.const_mul 2)) y
  convert (hd (2*x)).comp x ((hasDerivAt_id x).const_mul 2) using 1
  · rfl
  · dsimp only [potential,source]
    rw [show (2*x)/2=x by ring]
    ring

/-- Almost-everywhere equal densities have exactly the same actual Green potential.
Use: replaces a measurable equality density by its continuous potential-square representative.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the literal convolution integrands agree almost everywhere at every fixed center. -/
theorem potential_congr {m q : Density} (h : m.value=ᵐ[volume] q.value) : potential m=potential q := by
  funext x
  rw [potential_kernel,potential_kernel]
  exact integral_congr_ae (h.mono fun y hy => congrArg (fun r : ℝ => r*exp (-2*|x-y|)) hy)

/-- A square of an actual potential gives a continuous finite-energy density.
Use: equality densities have a representative with classical Green regularity.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def potentialSquare (m : Density) (c : ℝ) (hc : 0<c) : Density where
  value x := c^2*potential m x^2
  measurable := measurable_const.mul ((potential_continuous m).1.measurable.pow_const 2)
  nonneg x := mul_nonneg (sq_nonneg c) (sq_nonneg _)
  integrable := (potential_sobolev m).value_memLp.integrable_sq.const_mul (c^2)
  energy_integrable := by
    have he (x : ℝ) : (c^2*potential m x^2)^(3/2 : ℝ)=c^3*potential m x^3 := by
      rw [Real.rpow_div_two_eq_sqrt 3 (by positivity : 0≤c^2*potential m x^2),Real.rpow_ofNat,
        Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc.le,Real.sqrt_sq (potential_nonneg m x),mul_pow]
    simp_rw [he]
    exact (potential_cube_integrable m).const_mul (c^3)

/-- Every nonzero sharp Young equality potential satisfies its genuine classical semilinear equation.
Use: the first integral and Picard--Lindelof classify all equality cases.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: Holder rigidity supplies m=c²u² almost everywhere. Construct that actual
continuous density, identify its integral potential with the original one,
and transfer its classical second derivative and slope by derivative uniqueness. -/
theorem young_equality_classical (m : Density) (hm : 0<m.mass)
    (he : 18*(observe m .second)^3=5*m.energy^4) :
    ∃ c : ℝ, 0<c ∧ m.value=ᵐ[volume] (fun x => c^2*potential m x^2) ∧
      ∀ x, HasDerivAt (potentialSlope m) (4*potential m x-4*c^2*potential m x^2) x := by
  -- Regularity is deduced for every measurable equality density, rather than imposed on the theorem.
  obtain ⟨c,hc,_,hae⟩ := young_equality_potential m hm he
  let q := potentialSquare m c hc
  have hq : Continuous q.value := continuous_const.mul ((potential_continuous m).1.pow 2)
  have hp : potential m=potential q := potential_congr hae
  have hs : potentialSlope m=potentialSlope q := by
    funext x
    have h := potential_hasDerivAt m x
    rw [hp] at h
    exact h.unique (potential_hasDerivAt q x)
  refine ⟨c,hc,hae,fun x => ?_⟩
  rw [hs,hp]
  convert potential_second_derivative q hq x using 1
  change 4*potential q x-4*c^2*potential q x^2=4*potential q x-4*(c^2*potential m x^2)
  rw [hp]
  ring

end
end jacobi.Young
