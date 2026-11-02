import jacobi.Variational.SecondKKT
import jacobi.Variational.Congruence

/-!
Article: jacobi, Theorem D.5.
The actual second-moment minimizer has a continuous positive-part-square
representative. Its original exponential potential satisfies the genuine
classical clipped semilinear ODE. The coefficients and the continuous
representative are derived from the proved KKT theorem, rather than imposed
as a stationary-profile or differential-equation certificate.
Source: the normal multiplier rule and the actual exponent-two Green equation.
Use: gives a canonical classical representative of every actual second-moment optimizer.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The continuous positive-part-square density selected by the second-moment Euler equation.
Use: gives a canonical classical representative of every actual second-moment optimizer.
Article: jacobi, Theorem D.5.
-/
def eulerDensity (m : Density) (μ l : ℝ) (x : ℝ) : ℝ :=
  (4/9:ℝ)*(max (2*μ*potential m x-l) 0)^2

/-- The Euler density is continuous for every actual source density.
Use: the source Green equation becomes classical everywhere on the real line.
Article: jacobi, Theorem D.5.
Proof: the actual potential is continuous and so are maximum, squaring and scalar multiplication. -/
theorem eulerDensity_continuous (m : Density) (μ l : ℝ) : Continuous (eulerDensity m μ l) := by
  unfold eulerDensity
  have hc : Continuous (fun x => 2*μ*potential m x-l) :=
    (continuous_const.mul (potential_continuous m).1).sub continuous_const
  exact continuous_const.mul ((hc.max continuous_const).pow 2)

/-- The proved square-root Euler equation determines the actual density almost everywhere.
Use: retains all original variational and spectral data while replacing the source by its continuous formula.
Article: jacobi, Theorem D.5.
Proof: square the a.e. equation and use sqrt(m)²=m on the nonnegative density branch. -/
theorem eulerDensity_ae (m : Density) (μ l : ℝ)
    (he : (fun x => sqrt (m.value x))=ᵐ[volume]
      fun x => (2/3:ℝ)*max (2*μ*potential m x-l) 0) :
    m.value=ᵐ[volume] eulerDensity m μ l := by
  filter_upwards [he] with x hx
  have h := congrArg (fun r : ℝ => r^2) hx
  rw [Real.sq_sqrt (m.nonneg x)] at h
  change m.value x=(4/9:ℝ)*max (2*μ*potential m x-l) 0^2
  nlinarith

/-- The original potential obeys its actual classical clipped semilinear equation after KKT.
Use: supplies the elliptic first integral and exact quadrature derivation with no assumed weak-to-classical upgrade.
Article: jacobi, Theorem D.5.
Proof: replace the density by its proved continuous a.e. representative.
The actual integral potential is unchanged; uniqueness of its first derivative
identifies the slope, and the proved classical Green equation gives the ODE. -/
theorem eulerPotential_classical (m : Density) (μ l : ℝ)
    (he : m.value=ᵐ[volume] eulerDensity m μ l) :
    ∀ x,HasDerivAt (potentialSlope m)
      (4*potential m x-(16/9:ℝ)*max (2*μ*potential m x-l) 0^2) x := by
  -- Classical regularity is a consequence of KKT for the original measurable minimizer.
  let q := m.replace (eulerDensity m μ l) (eulerDensity_continuous m μ l).measurable
    (fun _ => by unfold eulerDensity; positivity) he
  have hp : potential m=potential q := potential_congr he
  have hs : potentialSlope m=potentialSlope q := by
    funext x
    have h := potential_hasDerivAt m x
    rw [hp] at h
    exact h.unique (potential_hasDerivAt q x)
  intro x
  rw [hs]
  have h := potential_second_derivative q (eulerDensity_continuous m μ l) x
  rw [← hp] at h
  convert h using 1
  change 4*potential m x-(16/9:ℝ)*max (2*μ*potential m x-l) 0^2=
    4*potential m x-4*((4/9:ℝ)*max (2*μ*potential m x-l) 0^2)
  ring

/-- Every actual nonzero radial second-moment minimizer has a genuine classical clipped semilinear optimizer equation.
Use: the elliptic calibration starts its first-integral and quadrature chain from the attained original variational problem.
Article: jacobi, Theorem D.5.
Proof: construct the normal positive multipliers from actual minimality,
square their KKT formula and apply the proved Green regularity upgrade. -/
theorem second_minimizer_classical {M T : ℝ} (hT : 0<T) (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (hmM : m.mass≤M) (hmT : T≤observe m .second)
    (hmin : m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
      m.value=ᵐ[volume] eulerDensity m μ l ∧
      ∀ x,HasDerivAt (potentialSlope m)
        (4*potential m x-(16/9:ℝ)*max (2*μ*potential m x-l) 0^2) x := by
  -- No optimizer equation is supplied as a premise; the actual KKT theorem constructs it.
  obtain ⟨_,μ,l,hμ,hl,hcomp,he⟩ := second_minimizer_kkt hT m hm hrad hmM hmT hmin
  have hae := eulerDensity_ae m μ l he
  exact ⟨μ,l,hμ,hl,hcomp,hae,eulerPotential_classical m μ l hae⟩

end
end jacobi.Elliptic
