import jacobi.Keller.Euler
import jacobi.Variational.PositivePartCalculus

/-!
Article: jacobi, Theorem D.6.
The original minimizing density supplies integrability of the positive cube.
Together with actual H1 regularity this forces the conserved quantity's
constant to be zero. Evaluating at the genuine normalized peak determines
the amplitude and the shape c=1/(1-v_e), including the transition branch.
Source: the autonomous ground ODE, the proved positive-cube chain rule and integrability on the infinite line.
Use: derives the conserved-energy integrability from the actual original objective.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational
open chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false
variable {m : Density} {ell M : ℝ}

/-- The literal Euler density has a positive constant times the clipped cube as its energy integrand.
Use: derives the conserved-energy integrability from the actual original objective.
Article: jacobi, Theorem D.6.
Proof: evaluate the square root of b*t² on the nonnegative t branch and cube it. -/
theorem Profile.energy_integrand (p : Profile m ell M) (x : ℝ) :
    (p.b*(max (H1.rep p.u x^2-p.edge) 0)^2)^(3/2:ℝ)=
      (sqrt p.b)^3*(max (H1.rep p.u x^2-p.edge) 0)^3 := by
  rw [Real.rpow_div_two_eq_sqrt 3 (mul_nonneg p.b_pos.le (sq_nonneg _)),
    Real.rpow_ofNat,Real.sqrt_mul p.b_pos.le,Real.sqrt_sq (le_max_right _ _),mul_pow]

/-- The actual normalized Keller state's positive cube is integrable on the whole line.
Use: the constant in its first integral is proved zero rather than supplied as an endpoint hypothesis.
Article: jacobi, Theorem D.6.
Proof: transfer finite objective energy through the actual a.e. Euler density
identity and divide by its strictly positive amplitude. -/
theorem Profile.cube_integrable (p : Profile m ell M) :
    Integrable (fun x => (max (H1.rep p.u x^2-p.edge) 0)^3) := by
  have hi : Integrable (fun x => (p.b*(max (H1.rep p.u x^2-p.edge) 0)^2)^(3/2:ℝ)) :=
    m.energy_integrable.congr (p.density.fun_comp (fun r : ℝ => r^(3/2:ℝ)))
  simp_rw [p.energy_integrand] at hi
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (pow_pos (sqrt_pos.mpr p.b_pos) 3).ne') _).mp hi

/-- Every actual normalized Keller optimizer satisfies the exact zero first integral everywhere.
Use: determines the peak amplitude and the genuine square-root Jacobian for all Keller quadratures.
Article: jacobi, Theorem D.6.
Proof: differentiate the actual conserved expression, including at the clipping
boundary. Its derivative is zero by the genuine ground equation. All its
terms are integrable, so its constant value on the infinite line is zero. -/
theorem Profile.first_integral (p : Profile m ell M) (hell : 0<ell) (x : ℝ) :
    p.d x^2=H1.rep p.u x^2-(2*p.b/(3*ell))*(max (H1.rep p.u x^2-p.edge) 0)^3 := by
  -- Conservation is a pointwise classical derivative identity, not merely an a.e. formal multiplication.
  let W (y : ℝ) := p.d y^2-H1.rep p.u y^2+
    (2*p.b/(3*ell))*(max (H1.rep p.u y^2-p.edge) 0)^3
  have hW (y : ℝ) : HasDerivAt W 0 y := by
    convert ((p.equation y).pow 2).sub ((p.derivative y).pow 2) |>.add
      (((positiveCube_hasDerivAt (H1.rep p.u y^2-p.edge)).comp y
        (((p.derivative y).pow 2).sub_const p.edge)).const_mul (2*p.b/(3*ell))) using 1
    · rfl
    · field_simp [hell.ne']; ring
  have hconst (y : ℝ) : W y=W 0 := is_const_of_deriv_eq_zero
    (fun z => (hW z).differentiableAt) (fun z => (hW z).deriv) y 0
  have hi : Integrable W := (p.slope_sq_integrable.sub
    (H1.regular p.u).value_memLp.integrable_sq).add (p.cube_integrable.const_mul _)
  have hc : Integrable (fun _ : ℝ => W 0) := hi.congr (Eventually.of_forall hconst)
  have hz : W 0=0 := by simpa only [integrable_const_iff,isFiniteMeasure_iff,
    Real.volume_univ,lt_self_iff_false,or_false] using hc
  have hh := (hconst x).trans hz
  dsimp only [W] at hh
  linarith

/-- The normalized actual cutoff lies strictly below the genuine peak.
Use: the shape parameter c is finite and at least one in both optimizer branches.
Article: jacobi, Theorem D.6.
Proof: a cutoff at or above one would make the peak's zero first integral equal to 0=1. -/
theorem Profile.edge_lt_one (p : Profile m ell M) (hell : 0<ell) : p.edge<1 := by
  have hh := p.first_integral hell 0
  rw [p.center_slope,p.center] at hh
  by_contra hn
  rw [max_eq_right (by linarith : 1^2-p.edge≤0)] at hh
  norm_num at hh

/-- The actual finite Keller shape parameter determined by the optimizing ground cutoff.
Use: the exact quadratures and the unique mass equation all use this same c.
Article: jacobi, Theorem D.6.
-/
def Profile.shape (p : Profile m ell M) : ℝ := (1-p.edge)⁻¹

/-- The actual Keller shape is at least one.
Use: licenses the full-domain literal j_k(c) identities for every actual optimizer.
Article: jacobi, Theorem D.6.
Proof: 0<1-v_e<=1 and inversion reverses the positive order. -/
theorem Profile.shape_ge_one (p : Profile m ell M) (hell : 0<ell) : 1≤p.shape := by
  have he : 0<1-p.edge := sub_pos.mpr (p.edge_lt_one hell)
  exact (one_le_inv₀ he).mpr (by linarith [p.edge_nonneg])

/-- The true peak equation fixes the Euler amplitude exactly in terms of the source's shape c.
Use: eliminates the normal multiplier from the actual mass and energy quadratures.
Article: jacobi, Theorem D.6.
Proof: evaluate the zero first integral at u(0)=1,u'(0)=0 and cancel the positive cutoff gap. -/
theorem Profile.amplitude (p : Profile m ell M) (hell : 0<ell) :
    p.b=(3*ell/2)*p.shape^3 := by
  have hh := p.first_integral hell 0
  rw [p.center_slope,p.center,max_eq_left (by nlinarith [p.edge_lt_one hell] : 0≤1^2-p.edge)] at hh
  norm_num only [zero_pow (by decide : 2≠0),one_pow] at hh
  dsimp only [Profile.shape]
  have he : 1-p.edge≠0 := (sub_pos.mpr (p.edge_lt_one hell)).ne'
  field_simp [he,hell.ne'] at hh ⊢
  nlinarith

/-- The free-mass transition parameter is exactly the zero mass-multiplier branch.
Use: separates the two exhaustive branches of the Keller calibration.
Article: jacobi, Theorem D.6.
Proof: invert c=1/(1-v_e), using the proved positive cutoff gap. -/
theorem Profile.shape_eq_one_iff (p : Profile m ell M) : p.shape=1 ↔ p.edge=0 := by
  rw [Profile.shape,inv_eq_one]
  constructor <;> intro h <;> linarith

/-- Any actual Keller optimizer in the strict c>1 branch saturates the original mass bound.
Use: converts its quadrature identity into the printed unique defining mass equation.
Article: jacobi, Theorem D.6.
Proof: c>1 excludes a zero cutoff, so the proved actual mass complementarity forces equality. -/
theorem Profile.mass_saturated (p : Profile m ell M) (hc : 1<p.shape) : m.mass=M := by
  have he : p.edge≠0 := fun hz => hc.ne' (p.shape_eq_one_iff.mpr hz)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp p.complementarity).resolve_left he)).symm

end
end jacobi.Keller
