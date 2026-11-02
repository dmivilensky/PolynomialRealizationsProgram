import krylov.XR.ThresholdMoments
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: main_krylov, thm:metric, general robust least-squares path.
Use: supply the actual norm differential and one-sided optimality used
to identify the Newton/zero thresholds and the intermediate regularizer.
Source: elementary Hilbert-space differentiation; the path is cited in
the article to Chandrasekaran et al. (1998), Theorem 3.6, and El Ghaoui--
Lebret (1997). All analytical implications used here are proved in Lean.
-/
namespace krylov.XR
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual norm derivative at a nonzero real Hilbert vector.
Article: main_krylov, thm:metric, robust optimality. -/
theorem robust_hasFDerivAt_norm (v : E) (hv : v≠0) :
    HasFDerivAt (fun x : E=>‖x‖) (‖v‖⁻¹ • innerSL ℝ v) v := by
  have hn := norm_ne_zero_iff.mpr hv
  have hh := (hasStrictFDerivAt_norm_sq v).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  convert hh using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg x)).symm
  · ext x
    simp only [_root_.smul_apply,smul_eq_mul,two_smul,_root_.add_apply,Real.sqrt_sq (norm_nonneg v)]
    field_simp
    ring

/-- Right-sided scalar minimality forces a nonnegative actual derivative.
Article: main_krylov, thm:metric, endpoint thresholds. -/
theorem robust_right_min_deriv_nonneg (f : ℝ → ℝ) (df : ℝ)
    (hmin : IsMinOn f (Ici 0) 0) (hf : HasDerivAt f df 0) : 0≤df := by
  have ht : (1:ℝ)∈posTangentConeAt (Ici (0:ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add,segment_eq_Icc (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Ici_self
  have hh := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hf.hasFDerivAt.hasFDerivWithinAt ht
  simpa using hh

/-- The original reduced robust objective for an arbitrary actual
positive self-adjoint model. Article: main_krylov, s8:minimax. -/
def robustModelObjective (N : E →L[ℝ] E) (rho : E) (omega : ℝ) (b : E) : ℝ :=
  ‖rho+N b‖+omega*‖b‖

/-- Away from both endpoint branches, the true robust objective has the
literal sum of the residual and correction norm derivatives.
Article: main_krylov, thm:metric, intermediate Tikhonov branch. -/
theorem robustModelObjective_hasFDerivAt (N : E →L[ℝ] E) (rho b : E) (omega : ℝ)
    (hb : b≠0) (hr : rho+N b≠0) :
    HasFDerivAt (robustModelObjective N rho omega)
      ((‖rho+N b‖⁻¹ • innerSL ℝ (rho+N b)).comp N+
        omega • (‖b‖⁻¹ • innerSL ℝ b)) b := by
  have hh := (robust_hasFDerivAt_norm _ hr).comp b
    ((hasFDerivAt_const rho b).add (N.hasFDerivAt (x:=b)))
  have hp := (robust_hasFDerivAt_norm b hb).const_mul omega
  convert hh.add hp using 1
  · rfl
  · simp only [zero_add]

end
end krylov.XR
