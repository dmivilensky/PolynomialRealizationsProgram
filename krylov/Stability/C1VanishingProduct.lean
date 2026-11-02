import krylov.Stability.FirstOrderTaylor
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Normed.Operator.Asymptotics
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch, C-one actual-increment remainder calculus.
Use: retain the real increments in the leading term and freeze only smooth
coefficients, obtaining a quadratic remainder from primitive C-one data.
Source: Mathlib differentiability implies first-order big-O, the operator norm
bound and the exact product difference identity; no C-two Taylor premise. -/

namespace krylov.Stability
noncomputable section
open Filter Topology Asymptotics
variable {X E F G α : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Genuine operator application multiplies two actual real big-O bounds.
Use: propagate true first-order vanishing factors into second-order remainders.
Article: main_krylov, prop:launch and thm:local.
Proof: the real operator norm bounds the actual application by the product
of both norms; multiply the supplied genuine scalar asymptotic estimates. -/
theorem clm_apply_bigO {l : Filter α} (A : α → E →L[ℝ] F) (v : α → E)
    (a b : α → ℝ) (hA : A =O[l] a) (hv : v =O[l] b) :
    (fun z => A z (v z)) =O[l] (fun z => a z*b z) := by
  have hnorm : (fun z => A z (v z)) =O[l] (fun z => ‖A z‖*‖v z‖) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall (fun z => by
      simpa only [one_mul,Real.norm_eq_abs,abs_mul,abs_norm] using (A z).le_opNorm (v z))
  exact hnorm.trans (hA.norm_left.mul hv.norm_left)

/-- Freezing the true smooth outer coefficient and input around a genuinely
vanishing middle operator leaves a quadratic remainder in the actual parameter.
Use: the original launch formula needs C-one primitive data and actual
increments, without replacing increments by derivatives or requiring C-two.
Article: main_krylov, prop:launch.
Proof: split the exact product difference into two terms. Each contains two
actual first-order vanishing factors, proved by genuine differentiability;
the remaining input is bounded by its actual continuity. -/
theorem c1_vanishing_middle_remainder
    (L : X → F →L[ℝ] G) (D : X → E →L[ℝ] F) (v : X → E)
    (hL : DifferentiableAt ℝ L 0) (hD : DifferentiableAt ℝ D 0)
    (hv : DifferentiableAt ℝ v 0) (hzero : D 0=0) :
    (fun z => L z (D z (v z))-L 0 (D z (v 0))) =O[𝓝 0] (fun z => ‖z‖^2) := by
  have hLs : (fun z => L z-L 0) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using hL.isBigO_sub.norm_right
  have hDs : D =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hzero,sub_zero] using hD.isBigO_sub.norm_right
  have hvs : (fun z => v z-v 0) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using hv.isBigO_sub.norm_right
  have hvb : v =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    isBigO_const_of_tendsto hv.continuousAt (by norm_num)
  have hfirst := clm_apply_bigO (fun z => L z-L 0) (fun z => D z (v z)) _ _ hLs
    (clm_apply_bigO D v _ _ hDs hvb)
  have hsecond := (L 0).isBigO_comp (fun z => D z (v z-v 0)) (𝓝 0) |>.trans
    (clm_apply_bigO D (fun z => v z-v 0) _ _ hDs hvs)
  simp only [mul_one] at hfirst
  have hsum := hfirst.add hsecond
  simpa only [← sq,_root_.sub_apply, map_sub,sub_add_sub_cancel] using hsum

end
end krylov.Stability
