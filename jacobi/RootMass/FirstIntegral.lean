import jacobi.RootMass.Boundary
import jacobi.RootMass.NodeGeometry

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
Conservation is proved on the actual compact core, then its constant is
fixed by the proved true Green boundary slope. The central zero slope
identifies the genuine upper turning point with the constructed inverse.
Source: the autonomous Green equation, actual boundary matching and psi bijectivity.
Use: its proved zero value yields the spatial square-root Jacobian.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The conserved expression of the actual root-mass optimizer on its compact core.
Use: its proved zero value yields the spatial square-root Jacobian.
Article: jacobi, Theorem D.8.
-/
def Profile.Y {a b T : ℝ} (P : Profile a b T) (x : ℝ) : ℝ :=
  P.D x^2-(2*P.C x+a)^2+P.kappa*(P.state x^3-P.state x)

/-- The actual compact optimizer's inverse first-integral parameter.
Use: the turning inverse and all four printed quadratures use this same positive parameter.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def Profile.y {a b T : ℝ} (P : Profile a b T) : ℝ := P.kappa⁻¹

/-- The actual conserved expression has zero classical derivative inside the positive half-core.
Use: mean values and actual endpoint matching determine the conserved constant.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: differentiate the original Green coefficient, its actual local
second derivative and the proved branch Jacobian. The literal ODE cancels
all terms, with the positive branch denominator nonzero. -/
theorem Profile.Y_hasDerivAt {a b T : ℝ} (P : Profile a b T) (hb : 0<b)
    {x : ℝ} (hx : x∈Ioo (0:ℝ) P.radius) : HasDerivAt P.Y 0 x := by
  -- Conservation follows from the actual integral potential and actual scalar branch.
  have hxcore : |x|≤P.radius := by rw [abs_of_pos hx.1]; exact hx.2.le
  have hdx := P.D_hasDerivAt hb (show x∈Ioo (-P.radius) P.radius from ⟨by linarith [P.radius_pos,hx.1],hx.2⟩)
  have hnx := P.state_hasDerivAt hb hxcore
  have hn := P.state_ge_one hb hxcore
  have hden : 3*P.state x^2-1≠0 := by nlinarith
  convert (((hdx.pow 2).sub ((((P.C_hasDerivAt x).const_mul 2).add_const a).pow 2)).add
    (((hnx.pow 3).sub hnx).const_mul P.kappa)) using 1
  · rfl
  · field_simp
    ring_nf
    have hc : (-1+P.state x^2*3)*(-1+P.state x^2*3)⁻¹=1 :=
      mul_inv_cancel₀ (by nlinarith)
    nlinarith [congrArg (fun r : ℝ => 2*P.D x*P.kappa*P.state x^2*r) hc]

/-- The actual first-integral constant is zero throughout the full closed half-core.
Use: fixes both the central turning level and the true square-root spatial slope.
Article: jacobi, Theorem D.8.
Proof: the actual expression is continuous on the closed core and has zero
derivative in its interior. Mean values give both monotonicity directions.
The true Green boundary slope and branch value make its boundary value zero. -/
theorem Profile.Y_zero {a b T : ℝ} (P : Profile a b T) (hb : 0<b)
    {x : ℝ} (hx : x∈Icc (0:ℝ) P.radius) : P.Y x=0 := by
  -- Use continuity at the jump boundary without asserting a classical second derivative there.
  have hC : Continuous P.C := continuous_iff_continuousAt.mpr fun t => (P.C_hasDerivAt t).continuousAt
  have hD : Continuous P.D := continuous_const.mul (potential_continuous P.density.toDensity).2
  have hc : Continuous P.Y := ((hD.pow 2).sub (((continuous_const.mul hC).add continuous_const).pow 2)).add
    (continuous_const.mul ((P.state_continuous.pow 3).sub P.state_continuous))
  have hd (t : ℝ) (ht : t∈interior (Icc (0:ℝ) P.radius)) :
      HasDerivWithinAt P.Y 0 (interior (Icc (0:ℝ) P.radius)) t :=
    (P.Y_hasDerivAt hb (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) P.radius) hc.continuousOn hd (fun _ _ => le_rfl)
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) P.radius) hc.continuousOn hd (fun _ _ => le_rfl)
  have he := le_antisymm (hmono hx ⟨P.radius_pos.le,le_rfl⟩ hx.2) (hanti hx ⟨P.radius_pos.le,le_rfl⟩ hx.2)
  have hCb : P.C P.radius=2 := by unfold Profile.C; rw [P.boundary]; field_simp
  rw [he]
  unfold Profile.Y
  rw [P.D_boundary hb,hCb,P.state_boundary hb]
  ring

/-- The parameter constructed from the actual normal multiplier is strictly positive.
Use: the true turning profile lies in the positive quadrature parameter domain.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: both the actual normal multiplier and b are strictly positive. -/
theorem Profile.y_pos {a b T : ℝ} (P : Profile a b T) (hb : 0<b) : 0<P.y := by
  unfold Profile.y Profile.kappa
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) P.mu_pos) hb)

/-- The actual compact optimizing branch satisfies the exact turning radicand identity.
Use: gives the true square-root Jacobian and the actual peak equation.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: multiply the proved zero conserved energy by nhat². Its stationary
identity identifies nhat*(2*C+a)=p(nhat), giving exactly the printed polynomial radicand. -/
theorem Profile.first_integral {a b T : ℝ} (P : Profile a b T) (hb : 0<b)
    {x : ℝ} (hx : x∈Icc (0:ℝ) P.radius) :
    P.state x^2*P.D x^2=radicand a P.y (P.state x) := by
  -- All quantities belong to the original attained profile.
  have hxcore : |x|≤P.radius := by rw [abs_of_nonneg hx.1]; exact hx.2
  have hs := P.stationary hb hxcore
  have hc : P.state x*(2*P.C x+a)=p a (P.state x) := by unfold p; nlinarith
  have hsq := congrArg (fun r : ℝ => r^2) hc
  have hy := congrArg (fun r : ℝ => P.state x^2*r) (P.Y_zero hb hx)
  dsimp only [Profile.Y] at hy
  unfold radicand Profile.y
  rw [div_inv_eq_mul]
  nlinarith

/-- The actual optimizer's central branch value is the unique true inverse turning point.
Use: identifies the spatial interval image with the same n_0(y) used in the printed quadratures.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: actual evenness gives zero central slope, so the proved first
integral gives psi(nhat(0))=y. The actual inverse bijection then identifies the peak. -/
theorem Profile.peak {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b) :
    P.state 0=inverse a ha P.y := by
  -- The turning parameter is derived from the actual first integral, never chosen to fit a candidate.
  have h0 : (0:ℝ)∈Icc 0 P.radius := ⟨le_rfl,P.radius_pos.le⟩
  have hcore0 : |(0:ℝ)|≤P.radius := by rw [abs_zero]; exact P.radius_pos.le
  have hn := P.state_ge_one hb hcore0
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  have hfi := P.first_integral hb h0
  rw [P.D_zero] at hfi
  have hpsi : psi a (P.state 0)=P.y := by
    unfold radicand at hfi
    unfold psi
    have hyp := P.y_pos hb
    field_simp at hfi ⊢
    nlinarith
  rw [← hpsi,inverse_psi ha hn]

end
end jacobi.RootMass
