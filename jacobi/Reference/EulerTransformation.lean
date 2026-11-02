import jacobi.Reference.HypergeometricUniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
Euler's transformation is proved for the actual community Gauss
hypergeometric function throughout its open unit disk, including
terminating numerator parameters. The actual analytic differential
equation and regular uniqueness fix the normalization at zero.
Source: Euler's hypergeometric transformation, DLMF 15.8.1; proved here.
Use: every actual power and derivative in Euler's transformation uses the original analytic branch.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The physical unit disk keeps 1-z strictly in the complex slit plane and away from zero.
Use: every actual power and derivative in Euler's transformation uses the original analytic branch.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: Re(z)<=|z|<1 gives Re(1-z)>0. -/
theorem one_sub_slitPlane {z : ℂ} (hz : ‖z‖<1) : 1-z∈Complex.slitPlane := by
  left
  simp only [sub_re,one_re]
  linarith [Complex.re_le_norm z]

/-- The actual analytic factor (1-z)^d and its genuine derivative on the unit disk.
Use: verifies the transformed Gauss equation in euler_equation.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the slit-plane power rule and the ordinary affine chain rule apply to the proved branch. -/
theorem one_sub_cpow_hasDerivAt (d : ℂ) {z : ℂ} (hz : ‖z‖<1) :
    HasDerivAt (fun w : ℂ => (1-w)^d) (-d*(1-z)^(d-1)) z := by
  convert! ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).cpow_const
    (c := d) (one_sub_slitPlane hz) using 1
  simp

/-- The actual Euler power factor is analytic on the entire original convergence disk.
Use: the transformed actual hypergeometric function has an analytic germ at zero and admits the identity theorem throughout the disk.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: its genuine complex derivative exists on the open disk; the community Cauchy theorem gives analyticity there. -/
theorem one_sub_cpow_analytic (d : ℂ) {z : ℂ} (hz : ‖z‖<1) :
    AnalyticAt ℂ (fun w : ℂ => (1-w)^d) z := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => (1-w)^d) (Metric.ball 0 1) :=
    fun w hw => (one_sub_cpow_hasDerivAt d (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball,dist_zero_right] using hz))

/-- The literal Euler transform solves exactly the original Gauss differential equation.
Use: regular analytic uniqueness proves euler_transform for the actual functions and exact normalization.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: Gauss's differential equation and Euler's transformation, DLMF 15.10.1 and 15.8.1.
Proof: differentiate the actual power-times-Gauss function twice.
The two shifted powers are the original power divided by 1-z and
(1-z)^2. After collecting terms the residual is that same power times
the proved Gauss residual with parameters c-a,c-b,c, hence zero. -/
theorem euler_equation {a b c z : ℂ} (hc : 0<c.re) (hz : ‖z‖<1) :
    let Y : ℂ → ℂ := fun w => (1-w)^(c-a-b)*ordinaryHypergeometric (c-a) (c-b) c w
    z*(1-z)*deriv (deriv Y) z+(c-(a+b+1)*z)*deriv Y z-a*b*Y z=0 := by
  -- Keep the true derivatives separate until the two elementary power identities are applied.
  let d := c-a-b
  let U : ℂ → ℂ := ordinaryHypergeometric (c-a) (c-b) c
  let Y : ℂ → ℂ := fun w => (1-w)^d*U w
  let S : ℂ → ℂ := fun w => -d*(1-w)^(d-1)*U w+(1-w)^d*deriv U w
  have hU (w : ℂ) (hw : ‖w‖<1) : AnalyticAt ℂ U w := analytic hw
  have hY (w : ℂ) (hw : ‖w‖<1) : HasDerivAt Y (S w) w := by
    have hh := (one_sub_cpow_hasDerivAt d hw).mul (hU w hw).differentiableAt.hasDerivAt
    convert! hh using 1
  have hS := (((one_sub_cpow_hasDerivAt (d-1) hz).const_mul (-d)).mul
    (hU z hz).differentiableAt.hasDerivAt).add
      ((one_sub_cpow_hasDerivAt d hz).mul (hU z hz).deriv.differentiableAt.hasDerivAt)
  change HasDerivAt S _ z at hS
  have hlocal : deriv Y=ᶠ[𝓝 z] S := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (show z∈Metric.ball 0 1 by simpa only [Metric.mem_ball,dist_zero_right] using hz)] with w hw
    exact (hY w (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).deriv
  change z*(1-z)*deriv (deriv Y) z+(c-(a+b+1)*z)*deriv Y z-a*b*Y z=0
  rw [hlocal.deriv_eq,hS.deriv,(hY z hz).deriv]
  have hbase : 1-z≠0 := by
    intro h
    have he : z=1 := (sub_eq_zero.mp h).symm
    simp only [he,norm_one,lt_self_iff_false] at hz
  have h1 : (1-z)^(d-1)=(1-z)^d/(1-z) := by
    rw [Complex.cpow_sub _ _ hbase,Complex.cpow_one]
  have h2 : (1-z)^(d-1-1)=(1-z)^d/(1-z)^2 := by
    rw [show d-1-1=d-2 by ring,Complex.cpow_sub _ _ hbase,Complex.cpow_ofNat]
  have hEq := equation (a := c-a) (b := c-b) hc hz
  change z*(1-z)*deriv (deriv U) z+(c-((c-a)+(c-b)+1)*z)*deriv U z-(c-a)*(c-b)*U z=0 at hEq
  dsimp [S,Y,Function.comp_apply]
  rw [h1,h2]
  field_simp [hbase]
  dsimp [d] at *
  linear_combination (1-z)*(1-z)^(c-a-b)*hEq

/-- Euler's exact transformation holds for the actual community hypergeometric functions on the whole open unit disk.
Use: identifies the beta-convolved cosine series with the original reference solution, with no unproved special-function identity.
Article: jacobi, Lemma C.1.
Source: Euler's transformation, DLMF 15.8.1; proved here from the original differential equations.
Proof: the two analytic functions have central value one and solve
the same genuine Gauss equation. Their difference has zero initial value
and zero residual, so gauss_zero_unique makes it vanish near zero.
The community identity theorem extends equality over the connected disk. -/
theorem euler_transform {a b c z : ℂ} (hc : 0<c.re) (hz : ‖z‖<1) :
    ordinaryHypergeometric a b c z=
      (1-z)^(c-a-b)*ordinaryHypergeometric (c-a) (c-b) c z := by
  -- All uniqueness hypotheses are verified for these two actual source functions.
  let F : ℂ → ℂ := ordinaryHypergeometric a b c
  let Y : ℂ → ℂ := fun w => (1-w)^(c-a-b)*ordinaryHypergeometric (c-a) (c-b) c w
  have hF (w : ℂ) (hw : ‖w‖<1) : AnalyticAt ℂ F w := analytic hw
  have hY (w : ℂ) (hw : ‖w‖<1) : AnalyticAt ℂ Y w :=
    (one_sub_cpow_analytic _ hw).mul (analytic hw)
  have hzero : (Y-F) 0=0 := by simp [Y,F]
  have heq : ∀ᶠ w : ℂ in 𝓝 0,
      w*(1-w)*deriv (deriv (Y-F)) w+(c-(a+b+1)*w)*deriv (Y-F) w-a*b*(Y-F) w=0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simp : (0:ℂ)∈Metric.ball 0 1)] with w hw
    have hw' : ‖w‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hw
    have hlocal : deriv (Y-F)=ᶠ[𝓝 w] (deriv Y-deriv F) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
      exact deriv_sub (hY v (by simpa only [Metric.mem_ball,dist_zero_right] using hv)).differentiableAt
        (hF v (by simpa only [Metric.mem_ball,dist_zero_right] using hv)).differentiableAt
    rw [hlocal.deriv_eq,deriv_sub (hY w hw').deriv.differentiableAt (hF w hw').deriv.differentiableAt,
      deriv_sub (hY w hw').differentiableAt (hF w hw').differentiableAt]
    simp only [Pi.sub_apply]
    linear_combination (euler_equation hc hw')-(equation (a := a) (b := b) hc hw')
  have hnear := gauss_zero_unique hc ((hY 0 (by norm_num)).sub (hF 0 (by norm_num))) hzero heq
  have hA : AnalyticOnNhd ℂ (Y-F) (Metric.ball 0 1) := fun w hw =>
    (hY w (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).sub
      (hF w (by simpa only [Metric.mem_ball,dist_zero_right] using hw))
  exact (sub_eq_zero.mp (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0:ℂ) 1).isPreconnected (by simp : (0:ℂ)∈Metric.ball 0 1) hnear
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz))).symm

end
end jacobi.Reference.Hypergeometric
