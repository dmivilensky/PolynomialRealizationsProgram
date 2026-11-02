import jacobi.Fredholm.Pole
import jacobi.Fredholm.GreenCongruence
import jacobi.Fredholm.RadialRepresentative
import jacobi.Fredholm.FirstIntegral

/-!
Article: jacobi, Theorem D.7.
The actual full-domain Fredholm minimizer is strictly subcritical, has an
active determinant constraint and proved normal multipliers. Its true Green
Euler representative is continuous and pointwise radial. Replacing null-set
values preserves its original operator, cost, mass and determinant exactly.
Source: the proved normal multiplier rule and actual Green-kernel congruence.
Use: gives classical Green regularity without a density-regularity premise on the original minimizer.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The literal continuous density selected by the actual Fredholm Euler equation.
Use: gives classical Green regularity without a density-regularity premise on the original minimizer.
Article: jacobi, Theorem D.7.
-/
def eulerValue (m : Density) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1) (mu ell x : ℝ) : ℝ :=
  (4/9:ℝ)*(max (mu*s*(2*m.fredholmGreen s hs hp x x-1)-ell) 0)^2

/-- The actual Fredholm Euler representative is continuous everywhere.
Use: upgrades the original measurable minimizer's Green diagonal to C2.
Article: jacobi, Theorem D.7.
Proof: the actual complete inverse Green kernel is continuous, including along its diagonal. -/
theorem eulerValue_continuous (m : Density) {s : ℝ} (hs : 0≤s) (hp : s*observe m .top<1) (mu ell : ℝ) :
    Continuous (eulerValue m s hs hp mu ell) := by
  have hg := (m.fredholmGreen_continuous hs hp).comp (continuous_id.prodMk continuous_id)
  exact continuous_const.mul ((((continuous_const.mul ((continuous_const.mul hg).sub continuous_const)).sub continuous_const).max continuous_const).pow 2)

/-- The original square-root KKT identity determines the actual optimizing density almost everywhere.
Use: constructs the true continuous Euler representative with all original variational data preserved.
Article: jacobi, Theorem D.7.
Proof: square the actual a.e. square-root identity and use m>=0. -/
theorem eulerValue_ae (m : Density) {s : ℝ} (hs : 0≤s) (hp : s*observe m .top<1) (mu ell : ℝ)
    (he : (fun x => sqrt (m.value x))=ᵐ[volume]
      fun x => (2/3:ℝ)*max (mu*s*(2*m.fredholmGreen s hs hp x x-1)-ell) 0) :
    m.value=ᵐ[volume] eulerValue m s hs hp mu ell := by
  filter_upwards [he] with x hx
  have hh := congrArg (fun r : ℝ => r^2) hx
  rw [sq_sqrt (m.nonneg x)] at hh
  unfold eulerValue
  nlinarith

/-- The actual canonical continuous Fredholm minimizer, with all Euler and admissibility data proved from the original problem.
Use: the Green first integral, profile classification and exact quadratures start from this actual attained minimum.
Article: jacobi, Theorem D.7.
-/
structure Optimizer (s M d : ℝ) where
  /-- The actual attaining finite-energy density. -/
  density : Density
  /-- Continuity follows from its true Green Euler representative. -/
  continuous : Continuous density.value
  /-- The continuous representative preserves the original radial class pointwise. -/
  radial : SymmetricDecreasing density.value
  /-- Positive threshold forces nonzero mass. -/
  mass_pos : 0<density.mass
  /-- The true mass constraint is retained. -/
  mass_le : density.mass≤M
  /-- Actual attainment of the literal extended-valued Fredholm problem. -/
  optimal : density.cost=fredholmInfimum s M (ENNReal.ofReal d)
  /-- Strict pole separation is a proved consequence of actual minimality. -/
  pole : s*observe density .top<1
  /-- The actual determinant constraint is active. -/
  active : density.fredholm s=ENNReal.ofReal d
  /-- The actual normal determinant multiplier. -/
  mu : ℝ
  /-- Strict positivity comes from the proved constraint qualification. -/
  mu_pos : 0<mu
  /-- The actual multiplier of the upper mass constraint. -/
  ell : ℝ
  /-- The upper mass multiplier is nonnegative. -/
  ell_nonneg : 0≤ell
  /-- The actual mass constraint has normal complementarity. -/
  complementary : ell*(M-density.mass)=0
  /-- The actual canonical density equals its original Green Euler expression everywhere. -/
  euler : ∀ hs : 0≤s,density.value=eulerValue density s hs pole mu ell

/-- Every strictly feasible positive Fredholm threshold has a genuine continuous radial optimizer with its complete proved normal Euler data.
Use: removes every optimizer, subcriticality, continuity and multiplier premise from the Fredholm calibration.
Article: jacobi, Theorem D.7.
Proof: construct an actual radial minimizer by the existing direct method.
The proved amplitude-pole argument gives subcriticality; the existing full
Fredholm multiplier rule supplies activity and normal multipliers. Its
continuous Euler representative preserves mass, cost, spectrum and the
actual inverse Green kernel, so it satisfies the Euler identity pointwise. -/
theorem optimizer_exists {s M d : ℝ} (hs : 0<s) (hM : 0<M) (hd : 0<d)
    (hfeas : ENNReal.ofReal d<fredholmTerm s M) : Nonempty (Optimizer s M d) := by
  -- The initial witness is an actual minimizer of the full extended determinant problem.
  obtain ⟨m,hrad,hm,hmM,hmd,hmin⟩ := fredholm_minimizer_exists hM hs (ENNReal.ofReal_pos.mpr hd) hfeas
  have hp := minimizer_subcritical hs m hm hmM hmin
  obtain ⟨hactive,mu,ell,hmu,hell,hcomp,he⟩ := fredholm_minimizer_kkt hs hd m hrad hp hmM hmd hmin
  have hae := eulerValue_ae m hs.le hp mu ell he
  let q := m.replace (eulerValue m s hs.le hp mu ell) (eulerValue_continuous m hs.le hp mu ell).measurable
    (fun _ => by unfold eulerValue; positivity) hae
  have hqcont : Continuous q.value := eulerValue_continuous m hs.le hp mu ell
  have hspec : q.spectrum=m.spectrum := (m.spectrum_congr hae).symm
  have hqmass : q.mass=m.mass := (m.mass_congr hae).symm
  have hqcost : q.cost=m.cost := congrArg ENNReal.ofReal (m.energy_congr hae).symm
  have hqp : s*observe q .top<1 := by change s*q.spectrum 0<1; rw [hspec]; exact hp
  have hqfred : q.fredholm s=m.fredholm s := by unfold L1Source.fredholm; rw [hspec]
  refine ⟨⟨q,hqcont,continuous_radial hrad hqcont hae,by rw [hqmass]; exact hm,
    by rw [hqmass]; exact hmM,hqcost.trans hmin,hqp,hqfred.trans hactive,
    mu,hmu,ell,hell,by rw [hqmass]; exact hcomp,?_⟩⟩
  intro hs'
  have hgreen := green_congr hae hs' hp hqp
  funext x
  change eulerValue m s hs' hp mu ell x=eulerValue q s hs' hqp mu ell x
  unfold eulerValue
  rw [hgreen]

end
end jacobi.Fredholm
