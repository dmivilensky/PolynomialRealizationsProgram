import jacobi.Variational.TopKKT
import jacobi.Variational.RadialTopGradient
import jacobi.Young.PotentialRegularity

/-!
Article: jacobi, Theorem D.6.
The proved normal top-eigenvalue KKT theorem supplies the optimizing density.
Ground-state simplicity identifies its selected eigenvector with the genuine
positive ground state. Normalizing its central value gives u(0)=1 and
m=b*(u²-v_e)_+². Absolute-continuous regularity upgrades the actual ground
equation to a classical equation everywhere for this continuous representative.
Source: the existing top KKT, positive ground state and absolutely continuous FTC.
Use: packages proved normalization, Euler equation and complementarity for the conserved-energy and quadrature chain.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational
open chebyshev2.Sobolev chebyshev2.Continuum chebyshev2.GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The normalized classical ground profile of an actual Keller minimizer.
Use: packages proved normalization, Euler equation and complementarity for the conserved-energy and quadrature chain.
Article: jacobi, Theorem D.6.
The existence theorem below constructs every field from an actual minimizer. -/
structure Profile (m : Density) (ell M : ℝ) where
  /-- The actual normalized ground vector in the reused H1 Hilbert space. -/
  u : H1
  /-- Its everywhere classical derivative. -/
  d : ℝ → ℝ
  /-- The positive squared Euler amplitude, denoted a² in the source. -/
  b : ℝ
  /-- The nonnegative cutoff level v_e of the ground square. -/
  edge : ℝ
  /-- The amplitude is strictly positive because the normal multiplier is positive. -/
  b_pos : 0<b
  /-- The mass multiplier gives a nonnegative cutoff. -/
  edge_nonneg : 0≤edge
  /-- The positive ground vector is normalized at its actual center. -/
  center : H1.rep u 0=1
  /-- Reflection symmetry makes its actual central derivative zero. -/
  center_slope : d 0=0
  /-- The actual ground representative is positive everywhere. -/
  positive : ∀ x,0<H1.rep u x
  /-- The actual normalized ground state is even. -/
  even : ∀ x,H1.rep u (-x)=H1.rep u x
  /-- The ground state strictly decreases at nonnegative radii. -/
  decreasing : StrictAntiOn (H1.rep u) (Ici 0)
  /-- Its derivative is strictly negative at every positive radius. -/
  slope_neg : ∀ x,0<x → d x<0
  /-- The stated slope is the genuine derivative at every point. -/
  derivative : ∀ x,HasDerivAt (H1.rep u) (d x) x
  /-- The genuine slope is square integrable on the whole line. -/
  slope_sq_integrable : Integrable (fun x => d x^2)
  /-- The original actual density equals its continuous Euler formula almost everywhere. -/
  density : m.value=ᵐ[volume] fun x => b*(max (H1.rep u x^2-edge) 0)^2
  /-- The normalized positive ground state satisfies the actual classical clipped equation everywhere. -/
  equation : ∀ x,HasDerivAt d ((1-(2/ell)*b*(max (H1.rep u x^2-edge) 0)^2)*H1.rep u x) x
  /-- The original mass complementarity survives normalization of the mass multiplier. -/
  complementarity : edge*(M-m.mass)=0

/-- The complete Keller Euler profile exists for every actual radial top-constrained minimizer.
Use: starts the Keller first-integral and exact quadrature chain without an assumed ODE or multiplier certificate.
Article: jacobi, Theorem D.6.
Proof: apply proved top KKT and the actual positive ground theorem. Simplicity
identifies the KKT eigenvector's squared gradient with a positive multiple
of the normalized ground square. Rescale the normal multipliers, square
the positive-part equation, and upgrade the a.e. ground equation by the
absolutely continuous FTC for its now continuous Euler right-hand side. -/
theorem optimizer_profile {ell M : ℝ} (hell : 0<ell) (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (hmM : m.mass≤M) (hmell : ell≤observe m .top)
    (hmin : m.cost=relaxedInfimum {Observation.top} M (fun _ => ell)) :
    observe m .top=ell ∧ Nonempty (Profile m ell M) := by
  -- The optimizing density and the spectral derivative belong to the same actual compact operator.
  obtain ⟨hactive,e,he,hTe,μ,l,hμ,hl,hcomp,hEuler⟩ := top_minimizer_kkt hell m hm hrad hmM hmell hmin
  have hne : ¬m.value=ᵐ[volume] (0 : ℝ → ℝ) := by
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
  let z := H1.rep G.u 0
  have hz : 0<z := G.positive 0
  let u : H1 := z⁻¹ • G.u
  let d (x : ℝ) := G.d x/z
  have hu (x : ℝ) : H1.rep u x=H1.rep G.u x/z := by rw [H1.rep_smul]; change z⁻¹*H1.rep G.u x=H1.rep G.u x/z; ring
  let B := 2*c^2*z^2
  have hB : 0<B := by dsimp only [B]; positivity
  have hgrad (x : ℝ) : topGradient e x=B*(H1.rep u x)^2 := by
    rw [hce,topGradient,H1.rep_smul,hu]
    dsimp only [B]
    field_simp [hz.ne']
  let a := (2/3:ℝ)*μ*B
  let ve := l/(μ*B)
  have ha : 0<a := by dsimp only [a]; positivity
  have hve : 0≤ve := div_nonneg hl (mul_pos hμ hB).le
  have hK (x : ℝ) : (2/3:ℝ)*max (μ*topGradient e x-l) 0=a*max (H1.rep u x^2-ve) 0 := by
    rw [hgrad]
    have hf : μ*(B*H1.rep u x^2)-l=(μ*B)*(H1.rep u x^2-ve) := by
      dsimp only [ve]
      field_simp [(mul_pos hμ hB).ne']
    have hmax : max ((μ*B)*(H1.rep u x^2-ve)) 0=(μ*B)*max (H1.rep u x^2-ve) 0 := by
      simpa only [mul_zero] using (mul_max_of_nonneg (H1.rep u x^2-ve) 0 (mul_pos hμ hB).le).symm
    rw [hf,hmax]
    dsimp only [a]
    ring
  have hdensity : m.value=ᵐ[volume] fun x => a^2*(max (H1.rep u x^2-ve) 0)^2 := by
    filter_upwards [hEuler] with x hx
    have hh := congrArg (fun r : ℝ => r^2) hx
    rw [Real.sq_sqrt (m.nonneg x),hK,mul_pow] at hh
    exact hh
  have hud (x : ℝ) : HasDerivAt (H1.rep u) (d x) x := by
    convert! (G.derivative x).div_const z using 1
    funext y
    exact hu y
  have hcoupling : groundParameter m.integrable m.nonneg=2/ell := by
    change 2/m.spectrum 0=2/ell
    exact congrArg (fun r : ℝ => 2/r) hactive
  have hdac : ∀ r t,AbsolutelyContinuousOnInterval d r t := fun r t =>
    by simpa only [d,div_eq_mul_inv,mul_comm] using (G.d_locallyAC r t).const_mul z⁻¹
  have hdae : ∀ᵐ x,HasDerivAt d
      ((1-(2/ell)*a^2*(max (H1.rep u x^2-ve) 0)^2)*H1.rep u x) x := by
    filter_upwards [G.ode,hdensity] with x hx hmx
    have hh := hx.div_const z
    rw [hcoupling,hmx] at hh
    convert! hh using 1
    rw [hu x]
    ring
  have hdc : Continuous (fun x => (1-(2/ell)*a^2*(max (H1.rep u x^2-ve) 0)^2)*H1.rep u x) := by
    have hh := H1.continuous_rep u
    fun_prop
  have hde := locallyAC_hasDerivAt_of_continuous hdac hdae hdc
  have hd2 : Integrable (fun x => d x^2) := by
    simpa only [d,div_pow] using G.d_memLp.integrable_sq.div_const (z^2)
  have heven := ground_even G hrad.even
  refine ⟨hactive,⟨⟨u,d,a^2,ve,sq_pos_of_pos ha,hve,?_,?_,?_,?_,?_,?_,hud,hd2,hdensity,hde,?_⟩⟩⟩
  · rw [hu,div_self hz.ne']
  · dsimp only [d]
    rw [heven.2,zero_div]
  · intro x
    rw [hu]
    exact div_pos (G.positive x) hz
  · intro x
    rw [hu,hu,heven.1]
  · intro x hx y hy hxy
    rw [hu,hu]
    exact div_lt_div_of_pos_right (ground_strictAnti G hrad hx hy hxy) hz
  · intro x hx
    exact div_neg_of_neg_of_pos (ground_slope_neg G hrad hx) hz
  · dsimp only [ve]
    rw [div_mul_eq_mul_div,hcomp,zero_div]

end
end jacobi.Keller
