import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: `main_krylov`, `thm:hier`, independent known-base and drift radii.
A genuine C² map which vanishes on its whole nearby zero-drift axis and
has zero derivative at the centre admits a mixed bound C*r*ω+C*ω².
The factor ω is obtained by the mean value theorem along the actual drift
segment; a joint quadratic or cubic Taylor bound alone does not retain it.
Source: local Lipschitz continuity of the true derivative and the vector
mean value inequality from mathlib.
-/

namespace krylov.Stability
noncomputable section
open Set Filter Topology Metric
variable {R P F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- True local zero-axis vanishing and a zero first jet give independent
prior/drift quadratic control, with one constant chosen before both radii. -/
theorem mixed_quadratic_of_zero_axis (f : R×P→F)
    (hf : ContDiffAt ℝ 2 f 0) (hd : HasFDerivAt f (0 : R×P→L[ℝ]F) 0)
    (haxis : ∀ᶠ z : R in 𝓝 0,f (z,0)=0) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ z : R,∀ E : P,‖z‖<δ → ‖E‖<δ →
      ‖f (z,E)‖≤C*‖z‖*‖E‖+C*‖E‖^2 := by
  obtain ⟨K,t,ht,hLip⟩ := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1≤2)).exists_lipschitzOnWith
  have hdiff : ∀ᶠ u : R×P in 𝓝 0,DifferentiableAt ℝ f u :=
    (hf.eventually (by norm_num)).mono (fun _ h ↦ h.differentiableAt (by norm_num))
  have haxis' : ∀ᶠ u : R×P in 𝓝 0,f (u.1,0)=0 := by
    have htend : Tendsto (fun u : R×P ↦ u.1) (𝓝 0) (𝓝 0) := continuousAt_fst.tendsto
    exact htend.eventually haxis
  have hgood : ∀ᶠ u : R×P in 𝓝 0,u∈t ∧ DifferentiableAt ℝ f u ∧ f (u.1,0)=0 := by
    filter_upwards [ht,hdiff,haxis'] with u hu hd' hz
    exact ⟨hu,hd',hz⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  have h0 := hball (show dist (0 : R×P) 0<δ by simpa using hδ)
  refine ⟨δ,(K : ℝ)+1,hδ,by positivity,?_⟩
  intro z E hz hE
  let r := max ‖z‖ ‖E‖
  have hr : r<δ := max_lt hz hE
  have hdiffball : ∀ u∈closedBall (0 : R×P) r,DifferentiableAt ℝ f u := by
    intro u hu
    exact (hball (lt_of_le_of_lt (by simpa only [mem_closedBall,dist_zero_right] using hu) hr)).2.1
  have hderiv : ∀ u∈closedBall (0 : R×P) r,
      ‖fderiv ℝ f u‖≤((K : ℝ)+1)*(‖z‖+‖E‖) := by
    intro u hu
    have hunorm : ‖u‖≤r := by simpa only [mem_closedBall,dist_zero_right] using hu
    have hut := (hball (by simpa only [dist_zero_right] using hunorm.trans_lt hr)).1
    have hh := hLip.norm_sub_le hut h0.1
    rw [hd.fderiv, sub_zero, sub_zero] at hh
    exact hh.trans (mul_le_mul (by linarith : (K : ℝ)≤(K : ℝ)+1)
      (hunorm.trans (max_le_add_of_nonneg (norm_nonneg z) (norm_nonneg E)))
      (norm_nonneg u) (by positivity))
  have hx : (z,(0 : P))∈closedBall (0 : R×P) r := by
    rw [mem_closedBall,dist_zero_right,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg z)]
    exact le_max_left _ _
  have hy : (z,E)∈closedBall (0 : R×P) r := by
    rw [mem_closedBall,dist_zero_right,Prod.norm_def]
  have hm := (convex_closedBall (0 : R×P) r).norm_image_sub_le_of_norm_fderiv_le
    hdiffball hderiv hx hy
  have hu : dist (z,E) (0 : R×P)<δ := by
    simpa only [dist_zero_right,Prod.norm_def] using hr
  have hzero : f (z,0)=0 := (hball hu).2.2
  rw [hzero,sub_zero] at hm
  calc
    _ ≤ ((K : ℝ)+1)*(‖z‖+‖E‖)*‖E‖ := by
      simpa only [Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_def,norm_zero,
        max_eq_right (norm_nonneg E)] using hm
    _ = _ := by ring

end
end krylov.Stability
