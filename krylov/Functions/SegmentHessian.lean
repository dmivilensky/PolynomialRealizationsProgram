import krylov.Nonlinear.CanonicalAverages
import Mathlib.Tactic.Module

/-!
Article: main_krylov, apG:sc(iii–iv), secants on arbitrary actual segments.
Use: retain the sharp half-weight of both endpoints and identify exactly the
midpoint of every affine Hessian. Reuses the genuine averagedDerivative integral.
Source: integral proof in Appendix G; Bochner integral calculus from mathlib.
-/

namespace krylov.Functions
noncomputable section
open Set MeasureTheory chebyshev1.Nonlinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The difference of segment points is a convex combination of endpoint differences.
Article: main_krylov, apG:sc(iii). Proof: affine vector algebra. -/
theorem segment_difference (a u b v : E) (t : ℝ) :
    (a + t • u) - (b + t • v) =
      (1 - t) • (a - b) + t • ((a + u) - (b + v)) := by module

/-- Compare two genuine segment averages with the sharp half-weight on each endpoint.
Article: main_krylov, apG:sc(iii).
Proof: integrate the convex endpoint bound, rather than a coarse maximum displacement. -/
theorem averagedHessian_endpoint_bound (H : E → E →L[ℝ] F) (a u b v : E) (L : ℝ)
    (ha : ContinuousOn (fun t : ℝ => H (a + t • u)) (Icc 0 1))
    (hb : ContinuousOn (fun t : ℝ => H (b + t • v)) (Icc 0 1))
    (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H (a + t • u) - H (b + t • v)‖ ≤ L * ‖(a + t • u) - (b + t • v)‖) :
    ‖averagedDerivative H a u - averagedDerivative H b v‖ ≤
      L / 2 * (‖a - b‖ + ‖(a + u) - (b + v)‖) := by
  rw [averagedDerivative, averagedDerivative, ← intervalIntegral.integral_sub
    (ha.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1))
    (hb.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1))]
  have hi : IntervalIntegrable
      (fun t : ℝ => L * ((1 - t) * ‖a - b‖ + t * ‖(a + u) - (b + v)‖)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun t : ℝ => H (a + t • u) - H (b + t • v))
    (g := fun t : ℝ => L * ((1 - t) * ‖a - b‖ + t * ‖(a + u) - (b + v)‖))
    (Filter.Eventually.of_forall fun t ht => by
      have ht₀ : 0 ≤ t := ht.1.le
      have ht₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      calc
        _ ≤ L * ‖(a + t • u) - (b + t • v)‖ := hlip t ⟨ht₀, ht.2⟩
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          rw [segment_difference]
          exact (norm_add_le _ _).trans_eq (by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg ht₁, abs_of_nonneg ht₀])) hL) hi
  convert hbound using 1
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (f := fun t : ℝ => (1 - t) * ‖a - b‖)
    (g := fun t : ℝ => t * ‖(a + u) - (b + v)‖)
    ((by fun_prop : Continuous _).intervalIntegrable 0 1)
    ((by fun_prop : Continuous _).intervalIntegrable 0 1),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
      (intervalIntegrable_const) (continuous_id.intervalIntegrable 0 1),
    intervalIntegral.integral_const, integral_id]
  norm_num
  ring

variable [CompleteSpace F]

/-- Every affine Hessian has exactly its midpoint value as its true segment secant.
Article: main_krylov, apG:sc(iv) and thm:struct.
Proof: integrate the constant and linear parts in the existing Bochner definition. -/
theorem averagedHessian_affine (H₀ : E →L[ℝ] F) (T : E →L[ℝ] E →L[ℝ] F) (a u : E) :
    averagedDerivative (fun x => H₀ + T x) a u = H₀ + T (a + (1 / 2 : ℝ) • u) := by
  unfold averagedDerivative
  simp only [map_add, map_smul]
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => H₀)
    (g := fun t : ℝ => T a + t • T u) (intervalIntegrable_const)
    ((by fun_prop : Continuous _).intervalIntegrable 0 1)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (f := fun _ : ℝ => T a) (g := fun t : ℝ => t • T u) (intervalIntegrable_const)
    ((by fun_prop : Continuous _).intervalIntegrable 0 1),
    intervalIntegral.integral_const, intervalIntegral.integral_smul_const, integral_id]
  norm_num

end
end krylov.Functions
