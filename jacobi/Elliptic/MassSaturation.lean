import jacobi.Elliptic.EulerEquation
import jacobi.Young.Equality

/-!
Article: jacobi, Theorem D.5.
The zero-mass-multiplier branch is classified using the already proved
classical semilinear uniqueness theorem: it is precisely the translated
Young family and has G_2/mass²=2/5. Consequently every actual elliptic-regime
minimizer has a strictly positive mass multiplier and uses its full mass.
Source: reuse of the complete Young profile classification and actual KKT complementarity.
Use: rules out the free-mass branch when the prescribed second-moment ratio exceeds 2/5.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- Every zero-mass-multiplier second-moment Euler profile is a translated Young density.
Use: rules out the free-mass branch when the prescribed second-moment ratio exceeds 2/5.
Article: jacobi, Theorem D.5.
Proof: positivity removes the clipping. The actual potential solves the
already classified decaying finite-energy equation u''=4u-a*u² with a>0.
Substitute its proved sech-square formula into the actual density equation. -/
theorem free_euler_young (m : Density) (hm : 0<m.mass) {μ : ℝ} (hμ : 0<μ)
    (he : m.value=ᵐ[volume] eulerDensity m μ 0) :
    ∃ b x₀ : ℝ,0<b ∧ m.value=ᵐ[volume] fun x => b*sech (x-x₀)^4 := by
  -- All ODE and endpoint hypotheses come from the original actual Green potential.
  let a := (64/9:ℝ)*μ^2
  have ha : 0<a := by dsimp only [a]; positivity
  have hode (x : ℝ) : HasDerivAt (potentialSlope m) (4*potential m x-a*potential m x^2) x := by
    have h := eulerPotential_classical m μ 0 he x
    have hc : 0≤2*μ*potential m x := mul_nonneg (by positivity) (potential_nonneg m x)
    rw [sub_zero,max_eq_left hc] at h
    convert h using 1
    dsimp only [a]
    ring
  obtain ⟨x₀,hprofile,_⟩ := semilinear_classification ha (potential_hasDerivAt m) hode
    (potential_sobolev m).value_memLp.integrable_sq (potential_sobolev m).derivative_memLp.integrable_sq
    (potential_cube_integrable m) (potential_sobolev m).tendsto_zero.1
    (potential_sobolev m).tendsto_zero.2 ⟨0,potential_pos m hm 0⟩
  refine ⟨(4/9:ℝ)*(2*μ*(6/a))^2,x₀,by positivity,?_⟩
  filter_upwards [he] with x hx
  have hc : 0≤2*μ*potential m x := mul_nonneg (by positivity) (potential_nonneg m x)
  change m.value x=(4/9:ℝ)*max (2*μ*potential m x-0) 0^2 at hx
  rw [sub_zero,max_eq_left hc,hprofile] at hx
  rw [hx]
  dsimp only [sechSquareSolution]
  ring

/-- The free-mass Euler branch has exactly the actual Young mass ratio.
Use: contradicts feasibility of this branch in the strict elliptic regime.
Article: jacobi, Theorem D.5.
Proof: classify the actual density, transfer mass and spectrum to its translated
literal Young representative, then substitute its already verified exact integrals. -/
theorem free_euler_mass_ratio (m : Density) (hm : 0<m.mass) {μ : ℝ} (hμ : 0<μ)
    (he : m.value=ᵐ[volume] eulerDensity m μ 0) :
    observe m .second=(2/5:ℝ)*m.mass^2 := by
  -- The ratio is evaluated on the actual operator spectrum of the original measurable density.
  obtain ⟨b,x₀,hb,hae⟩ := free_euler_young m hm hμ he
  let q := (equalityFamily b hb.le).translate x₀
  have hmq : m.value=ᵐ[volume] q.value := hae
  rw [observe_congr hmq,Density.mass_congr hmq,Density.translate_second,Density.translate_mass,
    equalityFamily_second,equalityFamily_mass]
  ring

/-- Every actual elliptic-regime second-moment minimizer has a positive mass multiplier and uses exactly its full mass.
Use: justifies the exact M normalization in the elliptic quadrature formula, without assuming mass activity.
Article: jacobi, Theorem D.5.
Proof: a zero mass multiplier would force the proved Young ratio 2/5,
contradicting 2M²<5T and mass(m)<=M. Positive multiplier complementarity
therefore forces the original mass constraint to be an equality. -/
theorem elliptic_mass_saturation {M T : ℝ} (hT : 0<T) (hregime : 2*M^2<5*T)
    (m : Density) (hm : 0<m.mass) (hrad : SymmetricDecreasing m.value)
    (hmM : m.mass≤M) (hmT : T≤observe m .second)
    (hmin : m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    m.mass=M ∧ ∃ μ l : ℝ,0<μ ∧ 0<l ∧ m.value=ᵐ[volume] eulerDensity m μ l := by
  -- The actual KKT theorem supplies both multipliers and the original measurable optimizer equation.
  obtain ⟨μ,l,hμ,hl,hcomp,hae,_⟩ := second_minimizer_classical hT m hm hrad hmM hmT hmin
  have hG := (second_minimizer_kkt hT m hm hrad hmM hmT hmin).1
  have hlpos : 0<l := by
    apply lt_of_le_of_ne hl
    intro hz
    have hfree : m.value=ᵐ[volume] eulerDensity m μ 0 := by simpa only [hz.symm] using hae
    have hratio := free_euler_mass_ratio m hm hμ hfree
    have hsq : m.mass^2≤M^2 := pow_le_pow_left₀ hm.le hmM 2
    rw [hG] at hratio
    nlinarith
  have hmass : m.mass=M := by
    have h := (mul_eq_zero.mp hcomp).resolve_left hlpos.ne'
    linarith
  exact ⟨hmass,μ,l,hμ,hlpos,hae⟩

end
end jacobi.Elliptic
