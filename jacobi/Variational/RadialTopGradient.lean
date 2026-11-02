import jacobi.Variational.RadialGround
import jacobi.Variational.TopVariation

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Every actual unit top eigenvector is a nonzero scalar multiple of the
strictly positive radial ground state. Its normalized squared gradient
is therefore positive, even and strictly decreasing at nonnegative radii.
This applies to the actual vector selected in the top multiplier theorem,
so no favorable choice of eigenvector is assumed in the shape statement.
Source: ground-state simplicity and the proved strict radial ground-state theorem.
Use: discharges the top branch of the single-moment optimality theorem's shape conclusion for its actual selected vector.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open chebyshev2.Sobolev chebyshev2.GroundState chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual unit top vector has the full positive, even and strictly decreasing spectral gradient.
Use: discharges the top branch of the single-moment optimality theorem's shape conclusion for its actual selected vector.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the actual ground residual identity makes the unit top vector a
nonzero scalar multiple of the positive ground state. Its square removes
the scalar sign, while strict positivity preserves strict square monotonicity. -/
theorem topGradient_radial (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {e : H1} (he : ‖e‖=1) (hTe : densityOperator m.value e=m.spectrum 0 • e) :
    (∀ x,0<topGradient e x) ∧ (∀ x,topGradient e (-x)=topGradient e x) ∧
      StrictAntiOn (topGradient e) (Ici 0) := by
  -- The same actual eigenvector as in the variation theorem is compared to the canonical positive ground state.
  have hne : ¬m.value=ᵐ[volume] 0 := by
    intro hz
    have hh : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae hz
    exact hm.ne' hh
  obtain ⟨G⟩ := ground_state m.integrable m.nonneg hne
  have hres : (∫ x,(H1.slope e x-G.R.a x*H1.rep e x)^2)=0 := by
    rw [G.R.square_identity m.integrable,density_ground_energy m.integrable m.nonneg hm hTe,sub_self]
  obtain ⟨c,hce⟩ := (G.R.residual_integral_eq_zero_iff_smul G.positive G.derivative e).mp hres
  have hc : c≠0 := by
    intro hz
    rw [hz,zero_smul] at hce
    rw [hce,norm_zero] at he
    exact zero_ne_one he
  have hformula (x : ℝ) : topGradient e x=2*c^2*(H1.rep G.u x)^2 := by
    rw [hce,topGradient,H1.rep_smul]
    ring
  refine ⟨fun x => by rw [hformula]; have hp := G.positive x; positivity,?_,?_⟩
  · intro x
    rw [hformula,hformula,(ground_even G hs.even).1]
  · intro x hx y hy hxy
    rw [hformula,hformula]
    have hu := ground_strictAnti G hs hx hy hxy
    have hsq : (H1.rep G.u y)^2<(H1.rep G.u x)^2 :=
      (sq_lt_sq₀ (G.positive y).le (G.positive x).le).mpr hu
    exact mul_lt_mul_of_pos_left hsq (mul_pos (by norm_num) (sq_pos_of_ne_zero hc))

/-- Every actual top gradient tends to zero at both ends of the line.
Use: positive mass multipliers give finite positive core intervals in the single-moment shape theorem.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the genuine H1 representative tends to zero at both ends, and its squared multiple is the literal gradient. -/
theorem topGradient_limits (e : H1) :
    Tendsto (topGradient e) atTop (𝓝 0) ∧ Tendsto (topGradient e) atBot (𝓝 0) := by
  unfold topGradient
  constructor
  · simpa only [zero_pow (by decide : 2≠0),mul_zero] using
      ((H1.rep_tendsto_zero e).1.pow 2).const_mul 2
  · simpa only [zero_pow (by decide : 2≠0),mul_zero] using
      ((H1.rep_tendsto_zero e).2.pow 2).const_mul 2

end
end jacobi.Variational
