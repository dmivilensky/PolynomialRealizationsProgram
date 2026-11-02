import jacobi.Variational.GreenMarkov
import chebyshev2.HalfLine.GroundConvolution
import jacobi.Young.PotentialRegularity

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual inverse column equals the free Green column plus the convolution
of its actual density source. For continuous densities this source is
continuous and integrable, so the smooth correction has a classical second
derivative. The two free exponential branches have the exact unit slope
jump; each full branch solves the genuine homogeneous Schrödinger equation.
Source: the actual resolvent equation and reused convolution regularity.
Use: convolution regularity turns the weak Green inverse into classical homogeneous branches.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open chebyshev2.Continuum chebyshev2.Sobolev chebyshev2.GroundState
open chebyshev2.HalfLine
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual source of a subcritical Green column in its free-kernel integral equation.
Use: convolution regularity turns the weak Green inverse into classical homogeneous branches.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenColumnSource (m : L1Source) (s : ℝ) (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) : ℝ := m.value y*m.fredholmGreen s hs hp x y

/-- Every actual Green column source is integrable on the full line.
Use: licenses the reused classical convolution and its two derivative formulas.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: identify the column with the actual H1 Green vector and use its uniform evaluation bound. -/
theorem L1Source.greenColumnSource_integrable (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) : Integrable (m.greenColumnSource s hs hp x) := by
  have h := density_rep_forcing_integrable m.integrable (m.fredholmGreenVector s hs hp x)
  change Integrable (fun y => m.value y*m.fredholmGreen s hs hp x y)
  simpa only [m.fredholmGreenVector_rep hs hp] using h

/-- Continuous actual densities give continuous Green-column sources.
Use: upgrades the absolutely continuous convolution slope to a classical derivative everywhere.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: multiply the continuous density by the continuous actual inverse column. -/
theorem L1Source.greenColumnSource_continuous (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) : Continuous (m.greenColumnSource s hs hp x) :=
  hc.mul ((m.fredholmGreen_continuous hs hp).comp (continuous_const.prodMk continuous_id))

/-- The actual inverse column satisfies its genuine free Green convolution equation.
Use: supplies both classical homogeneous branches and the exact slope jump at the source point.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply point evaluation to (I-s*K)G_x=k_x, identify the actual density
operator's representative with the already proved H1 convolution, and rearrange. -/
theorem L1Source.fredholmGreen_convolution (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) :
    m.fredholmGreen s hs hp x y=(1/2:ℝ)*exp (-|y-x|)+
      s*H1.rep (convolution (m.greenColumnSource s hs hp x)) y := by
  -- The convolution equation is deduced from the actual two-sided inverse, not assumed as an integral certificate.
  have h := congrArg (fun u : H1 => H1.rep u y) (m.pencil_resolvent hs hp (H1.k x))
  change H1.rep (m.fredholmGreenVector s hs hp x-
    s • densityOperator m.value (m.fredholmGreenVector s hs hp x)) y=H1.rep (H1.k x) y at h
  rw [jacobi.Continuum.h1Rep_sub,H1.rep_smul] at h
  dsimp only at h
  rw [m.fredholmGreenVector_rep hs hp,H1.k_rep,densityOperator_rep_convolution m.integrable] at h
  have he : (fun t => m.value t*H1.rep (m.fredholmGreenVector s hs hp x) t)=
      m.greenColumnSource s hs hp x := by
    funext t
    rw [m.fredholmGreenVector_rep hs hp]
    rfl
  rw [he] at h
  linarith

/-- The convolution correction of an actual Green column has a classical second derivative.
Use: each exponential branch then satisfies -phi''+(1-2s*m)*phi=0 away from the source.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the actual source is continuous and integrable. Apply the existing
absolutely-continuous FTC upgrade to its actual convolution slope. -/
theorem L1Source.greenColumn_convolution_second (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x y : ℝ) :
    HasDerivAt (convolutionSlope (m.greenColumnSource s hs hp x))
      (H1.rep (convolution (m.greenColumnSource s hs hp x)) y-2*m.greenColumnSource s hs hp x y) y := by
  have hi := m.greenColumnSource_integrable hs hp x
  exact locallyAC_hasDerivAt_of_continuous (convolutionSlope_locallyAC hi)
    (convolution_second_derivative_ae hi)
    ((H1.continuous_rep _).sub ((m.greenColumnSource_continuous hc hs hp x).const_mul 2)) y

/-- A globally smooth exponential extension of one side of the actual Green column.
Use: constructs local classical representatives of the homogeneous positive Green factors.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenBranch (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1)
    (x ρ y : ℝ) : ℝ := (1/2:ℝ)*exp (ρ*(y-x))+
      s*H1.rep (convolution (m.greenColumnSource s hs hp x)) y

/-- The actual slope of an exponential Green-column extension.
Use: gives its classical derivative and the exact source-point slope jump.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenBranchSlope (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1)
    (x ρ y : ℝ) : ℝ := (1/2:ℝ)*ρ*exp (ρ*(y-x))+
      s*convolutionSlope (m.greenColumnSource s hs hp x) y

/-- Each Green-column extension has its actual declared first derivative everywhere.
Use: transfers local factorization equalities to classical homogeneous solution derivatives.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: differentiate the elementary exponential and the proved actual H1 convolution. -/
theorem L1Source.greenBranch_hasDerivAt (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x ρ y : ℝ) :
    HasDerivAt (m.greenBranch s hs hp x ρ) (m.greenBranchSlope s hs hp x ρ y) y := by
  have he : HasDerivAt (fun t : ℝ => exp (ρ*(t-x))) (ρ*exp (ρ*(y-x))) y := by
    convert (((hasDerivAt_id y).sub_const x).const_mul ρ).exp using 1 <;> simp only [id_eq,mul_one,mul_comm]
  have h := (he.const_mul (1/2:ℝ)).add
    ((convolution_hasDerivAt (m.greenColumnSource_integrable hs hp x) y).const_mul s)
  convert h using 1
  · rfl
  · unfold L1Source.greenBranchSlope
    ring

/-- Both unit-sign branches have the exact classical second derivative with the actual Green forcing.
Use: after identifying a branch with G off its source, this is its homogeneous Schrodinger equation.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: differentiate the actual branch slope, use rho²=1 and the proved
continuous-source convolution equation, and collect the source term. -/
theorem L1Source.greenBranch_second (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x ρ y : ℝ) (hρ : ρ^2=1) :
    HasDerivAt (m.greenBranchSlope s hs hp x ρ)
      (m.greenBranch s hs hp x ρ y-2*s*m.greenColumnSource s hs hp x y) y := by
  -- The same integrable continuous source supplies both exponential extensions.
  have he : HasDerivAt (fun t : ℝ => exp (ρ*(t-x))) (ρ*exp (ρ*(y-x))) y := by
    convert (((hasDerivAt_id y).sub_const x).const_mul ρ).exp using 1 <;> simp only [id_eq,mul_one,mul_comm]
  have h := (he.const_mul ((1/2:ℝ)*ρ)).add ((m.greenColumn_convolution_second hc hs hp x y).const_mul s)
  convert h using 1
  · rfl
  · unfold L1Source.greenBranch
    linear_combination -(exp (ρ*(y-x))/2)*hρ

/-- On the right side, the negative-sign exponential extension equals the actual inverse column.
Use: the local representation of the globally positive right-decaying factor.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the free kernel exponent is -(y-x) when y>=x. -/
theorem L1Source.greenBranch_right (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) {x y : ℝ} (hxy : x≤y) :
    m.greenBranch s hs hp x (-1) y=m.fredholmGreen s hs hp x y := by
  rw [m.fredholmGreen_convolution hs hp]
  unfold L1Source.greenBranch
  rw [abs_of_nonneg (sub_nonneg.mpr hxy),neg_one_mul]

/-- On the left side, the positive-sign exponential extension equals the actual inverse column.
Use: the local representation of the globally positive left-decaying factor.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the free kernel exponent is y-x when y<=x. -/
theorem L1Source.greenBranch_left (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) {x y : ℝ} (hyx : y≤x) :
    m.greenBranch s hs hp x 1 y=m.fredholmGreen s hs hp x y := by
  rw [m.fredholmGreen_convolution hs hp]
  unfold L1Source.greenBranch
  rw [abs_of_nonpos (sub_nonpos.mpr hyx),neg_neg,one_mul]

/-- The two actual classical column slopes have exactly the unit delta-source jump.
Use: fixes the positive Wronskian normalization in the global Green product and diagonal identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the continuous convolution correction cancels, while the free exponential contributes one. -/
theorem L1Source.greenBranch_jump (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) :
    m.greenBranchSlope s hs hp x 1 x-m.greenBranchSlope s hs hp x (-1) x=1 := by
  simp only [L1Source.greenBranchSlope,sub_self,mul_zero,exp_zero,mul_one]
  ring

end
end jacobi.Variational
