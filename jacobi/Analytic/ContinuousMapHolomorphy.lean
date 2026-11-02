import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Continuous-function-valued holomorphy follows from norm continuity and
pointwise holomorphy by the Banach-valued Cauchy integral formula.
Source: Cauchy's formula and differentiation of Cauchy integrals,
as formalized in mathlib; evaluation commutes with the Bochner integral.
Use: lifts the scalar Cauchy identities of the genuine GL kernel to its Banach space of continuous kernels.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Evaluation of an actual continuous-function-valued circle integral is the circle integral of the pointwise values.
Use: lifts the scalar Cauchy identities of the genuine GL kernel to its Banach space of continuous kernels.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: the continuous-linear-map theorem for Bochner integrals in mathlib.
Proof: evaluation is a continuous complex linear map. Commute it with the defining interval integral and its complex scalar factors. -/
theorem continuousMap_circleIntegral_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : ℂ → C(X,ℂ)} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) (x : X) :
    (∮ z in C(c,r),f z) x=∮ z in C(c,r),f z x := by
  have hh := (ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm hf.out
  simpa only [circleIntegral,map_smul,ContinuousMap.evalCLM_apply] using hh.symm

/-- A norm-continuous family of continuous functions which is pointwise holomorphic on an open complex domain is holomorphic in the continuous-function norm.
Use: proves the genuine Banach holomorphy of the GL kernel, needed for analytic operator inversion and transformed profiles.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: the Banach-valued Cauchy integral argument, using mathlib's scalar Cauchy formula and differentiation under the circle integral.
Proof: inside any small closed disk the continuous-function-valued Cauchy integral is differentiable. Evaluation commutes with that integral; scalar Cauchy identities identify its value with the original family at every spatial point. This local equality transfers the Banach derivative to the genuine family. -/
theorem continuousMap_differentiableOn {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : ℂ → C(X,ℂ)} {U : Set ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hd : ∀ x : X,DifferentiableOn ℂ (fun z => f z x) U) :
    DifferentiableOn ℂ f U := by
  -- Point evaluations identify the Banach-valued Cauchy integral with the original family on a whole neighborhood.
  intro p hp
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let r : ℝ := ε/2
  have hr : 0<r := half_pos hε
  have hclosed : closedBall p r⊆U := (closedBall_subset_ball (by dsimp [r]; linarith)).trans hεU
  have hc : ContinuousOn f (closedBall p r) := hf.mono hclosed
  have hi : CircleIntegrable f p r := (hc.mono sphere_subset_closedBall).circleIntegrable hr.le
  let g := fun z => ((2*Real.pi*_root_.Complex.I:ℂ)⁻¹) • ∮ w in C(p,r),(w-z)⁻¹ • f w
  have hnot {z : ℂ} (hz : z∈ball p r) : z∉sphere p |r| := by
    rw [abs_of_pos hr]
    intro hs
    have hs' : dist z p=r := mem_sphere.mp hs
    have hz' : dist z p<r := mem_ball.mp hz
    linarith
  have hg0 := _root_.Complex.hasDerivAt_circleIntegral_sub_inv_smul hi (hnot (mem_ball_self hr))
  have hg : DifferentiableAt ℂ g p := (hg0.const_smul ((2*Real.pi*_root_.Complex.I:ℂ)⁻¹)).differentiableAt
  have heq : f=ᶠ[𝓝 p]g := by
    filter_upwards [ball_mem_nhds p hr] with z hz
    ext x
    have hij : CircleIntegrable (fun w => (w-z)⁻¹ • f w) p r := by
      simpa only [zpow_neg_one] using hi.sub_zpow_smul (-1) (hnot hz)
    change f z x=(((2*Real.pi*_root_.Complex.I:ℂ)⁻¹) •
      (∮ w in C(p,r),(w-z)⁻¹ • f w)) x
    rw [ContinuousMap.smul_apply,continuousMap_circleIntegral_apply hij x]
    exact (_root_.Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      countable_empty hz
      (((ContinuousMap.evalCLM ℂ x).continuous.comp_continuousOn hc))
      (fun w hw => ((hd x).differentiableAt (hU.mem_nhds
        (hclosed (ball_subset_closedBall hw.1)))))).symm
  exact (hg.congr_of_eventuallyEq heq).differentiableWithinAt

end
end jacobi.Analytic
