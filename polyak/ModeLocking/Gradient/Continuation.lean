import polyak.ModeLocking.Gradient.Graph
import polyak.ModeLocking.Continuation.Data

/-! Exact gradient and analytic zero graph for the continuation actually
constructed from the primary regularity conditions. -/
noncomputable section
namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Continuation _root_.polyak.ModeLocking.Gradient Filter
open scoped BigOperators Topology
variable {q:Tuning} {s:ℝ} {L:ℕ} {D:RegularData q s L} (C:D.ContinuationData)

theorem right_kernel_near : ∀ᶠp in 𝓝 (parameters q),
    (tightMatrix D.reps D.atoms (Gradient.continuedPoint C.shift p)).mulVec (C.primal p)=0 :=
  C.equations.mono fun _ hp=>hp.1

theorem weighted_gradient (v:Parameters) :
    fderiv ℝ C.shift (parameters q) v =
      -∑i,D.gradientWeight i*fderiv ℝ (sourceCotangent (D.atoms i)) (parameters q) v :=
  D.weighted_gradient_direction C.primalShift C.analytic_primalShift C.primalShift_base
    C.right_kernel_near v

theorem kappa_derivative_neg : fderiv ℝ C.shift (parameters q) kappaDirection<0 :=
  D.primal_kappa_derivative_neg C.primalShift C.analytic_primalShift C.primalShift_base C.right_kernel_near

theorem analytic_shift_zero_graph (hs:s=0) :
    ∃g:Plane→ℝ,AnalyticAt ℝ g (planeParameters q) ∧ g (planeParameters q)=q.kappa ∧
      (∀ᶠp in 𝓝 (planeParameters q),C.shift ![g p,p 0,p 1]=0) ∧
      ∀ᶠz:Plane×ℝ in 𝓝 (planeParameters q,q.kappa),C.shift (graphPoint z)=0 ↔g z.1=z.2 := by
  apply analytic_zero_graph (analyticAt_fst.comp C.analytic_primalShift)
  · exact (congrArg Prod.fst C.primalShift_base).trans hs
  · exact C.kappa_derivative_neg.ne

end polyak.ModeLocking.RegularData.ContinuationData
