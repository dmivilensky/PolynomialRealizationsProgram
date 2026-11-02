import jacobi.RootMass.Profile

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
The actual positive branch is continuous and even. Its stationary identity,
boundary value and true derivative are consequences of the literal larger
root, not assumptions about a formal solution of the profile equation.
Source: the exact scalar root and the derivative of the actual Green potential.
Use: differentiating this literal identity gives the normalized profile Jacobian.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual larger root satisfies its stationary identity whenever its radicand is nonnegative.
Use: differentiating this literal identity gives the normalized profile Jacobian.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: square the actual square root in the larger-root formula. -/
theorem upperRoot_stationary {b c : ℝ} (hD : 0≤c^2-3*b^2) :
    3*(upperRoot b c)^2-2*c*upperRoot b c+b^2=0 := by
  have hs := sq_sqrt hD
  unfold upperRoot
  nlinarith

/-- The actual normalized branch is continuous on the real line.
Use: includes the core endpoints in the first-integral matching and interval image.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: divide the continuous literal larger-root branch by its constant amplitude. -/
theorem Profile.state_continuous {a b T : ℝ} (P : Profile a b T) : Continuous P.state :=
  (branch_continuous P.density a b P.mu).div_const b

/-- The normalized branch inherits the actual optimizing potential's evenness.
Use: doubles the genuine positive half-core quadratures.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the scalar branch depends only on the even original Green potential. -/
theorem Profile.state_even {a b T : ℝ} (P : Profile a b T) (x : ℝ) : P.state (-x)=P.state x := by
  unfold Profile.state branch coefficient
  rw [potential_even P.density.toDensity P.radial]

/-- The actual coefficient stays above its switching value throughout the full closed core.
Use: fixes the positive square-root branch in every profile derivative.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: compare the absolute radius with the actual boundary using evenness and strict radial monotonicity. -/
theorem Profile.coefficient_ge {a b T : ℝ} (P : Profile a b T) {x : ℝ} (hx : |x|≤P.radius) :
    2*b≤coefficient P.density a b P.mu x := by
  -- The boundary case uses evenness; the interior uses the actual strict superlevel set.
  by_cases hi : |x|<P.radius
  · exact ((P.core x).mpr hi).le
  · have he : |x|=P.radius := le_antisymm hx (le_of_not_gt hi)
    have hs := (coefficient_shape P.density P.mass_pos P.radial a b P.mu_pos).2.1
    rcases le_total 0 x with hp | hn
    · rw [abs_of_nonneg hp] at he
      rw [he,P.boundary]
    · rw [abs_of_nonpos hn] at he
      rw [← hs x,he,P.boundary]

/-- The actual normalized branch is at least one on the closed positive core.
Use: all subsequent rational profile denominators are strictly positive.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: above the switching level the true larger root exceeds b; at the boundary it equals b. -/
theorem Profile.state_ge_one {a b T : ℝ} (P : Profile a b T) (hb : 0<b) {x : ℝ} (hx : |x|≤P.radius) :
    1≤P.state x := by
  -- The actual branch is above b in the interior and equals b at the switching level.
  have hc := P.coefficient_ge hx
  apply (le_div_iff₀ hb).mpr
  change 1*b≤upperRoot b (coefficient P.density a b P.mu x)
  rw [one_mul]
  rcases lt_or_eq_of_le hc with ht | he
  · exact (upperRoot_properties hb ht).1.le
  · rw [← he,upperRoot_switch hb.le]

/-- The actual normalized branch equals one at the proved free boundary.
Use: fixes the conserved first integral from actual Green matching.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: substitute the actual switching equation into the true larger-root formula. -/
theorem Profile.state_boundary {a b T : ℝ} (P : Profile a b T) (hb : 0<b) : P.state P.radius=1 := by
  unfold Profile.state branch
  rw [P.boundary,upperRoot_switch hb.le,div_self hb.ne']

/-- The normalized scalar stationary equation holds throughout the actual closed core.
Use: eliminates the Green coefficient from the true conserved energy.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: divide the true larger-root stationary equation by the positive amplitude squared. -/
theorem Profile.stationary {a b T : ℝ} (P : Profile a b T) (hb : 0<b) {x : ℝ} (hx : |x|≤P.radius) :
    3*P.state x^2-2*P.C x*P.state x+1=0 := by
  -- The true scalar stationary identity is divided by the positive amplitude squared.
  have hc := P.coefficient_ge hx
  have hD : 0≤(coefficient P.density a b P.mu x)^2-3*b^2 := by nlinarith
  have he := upperRoot_stationary hD
  unfold Profile.state Profile.C branch
  field_simp
  nlinarith

/-- The actual normalized profile has its exact classical Jacobian at every point of the closed core.
Use: the first integral and the genuine spatial change of variables use the original branch derivative.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the literal branch is differentiable because its radicand is positive
near each core point. Differentiate its true stationary identity there.
The positive normalized branch makes the resulting coefficient nonzero. -/
theorem Profile.state_hasDerivAt {a b T : ℝ} (P : Profile a b T) (hb : 0<b)
    {x : ℝ} (hx : |x|≤P.radius) :
    HasDerivAt P.state (2*P.state x^2*P.D x/(3*P.state x^2-1)) x := by
  -- The stationary identity is valid on an actual open neighborhood, including at core endpoints.
  let c := coefficient P.density a b P.mu
  have hc : HasDerivAt c (2*P.mu*potentialSlope P.density.toDensity x) x :=
    ((potential_hasDerivAt P.density.toDensity x).const_mul (2*P.mu)).const_add (-a*b/2)
  have hcg := P.coefficient_ge hx
  have hD : 0<c x^2-3*b^2 := by dsimp only [c]; nlinarith
  have hdif : DifferentiableAt ℝ P.state x := by
    exact (((hc.differentiableAt.add (((hc.pow 2).sub_const (3*b^2)).differentiableAt.sqrt hD.ne')).div_const 3).div_const b)
  have hd := hdif.hasDerivAt
  have hevent : (fun t => 3*P.state t^2-2*P.C t*P.state t+1)=ᶠ[𝓝 x] fun _ => 0 := by
    have hpos := ((hc.continuousAt.pow 2).sub continuousAt_const).eventually (Ioi_mem_nhds hD)
    filter_upwards [hpos] with t ht
    have he := upperRoot_stationary (le_of_lt ht)
    unfold Profile.state Profile.C branch
    field_simp
    nlinarith
  have hdpoly : HasDerivAt (fun t => 3*P.state t^2-2*P.C t*P.state t+1)
      (3*(2*P.state x*deriv P.state x)-2*(P.D x*P.state x+P.C x*deriv P.state x)) x := by
    convert! ((((hd.pow 2).const_mul 3).sub (((P.C_hasDerivAt x).mul hd).const_mul 2)).add_const 1) using 1
    · funext t
      dsimp only [Pi.pow_apply,Pi.sub_apply,Pi.mul_apply]
      ring
    · norm_num
  have hzero := (hdpoly.congr_of_eventuallyEq hevent.symm).unique (hasDerivAt_const x (0:ℝ))
  have hstat := P.stationary hb hx
  have hn := P.state_ge_one hb hx
  have hden : 0<3*P.state x^2-1 := by nlinarith
  convert hd using 1
  apply (div_eq_iff hden.ne').mpr
  nlinarith [congrArg (fun r : ℝ => deriv P.state x*r) hstat,
    congrArg (fun r : ℝ => P.state x*r) hzero]

end
end jacobi.RootMass
