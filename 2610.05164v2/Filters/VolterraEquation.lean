import «2610.05164v2».Filters.VolterraLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: 2610.05164v2, Theorem 6.1.
The series solves the actual Volterra integral equation, with the exchange of sum and integral
justified for a general L1 density.
Use: `«2610.05164v2».Filters.jost_equation` feeds `«2610.05164v2».HalfLine.jost_green_equation`
(jost green equation).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/--
The series solves the actual Volterra integral equation, with the exchange of sum and integral
justified for a general L1 density.

Exact identity `jost s m x=1+volterra s m (jost s m) x`.

Use: `«2610.05164v2».Filters.jost_hasDerivAt` uses this identity to establish the actual
derivative at the stated point: `HasDerivAt (jost s m) (jostSlope s m x) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem jost_equation {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : jost s m x=1+volterra s m (jost s m) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let F : ℕ → ℝ → ℝ := fun n t => (1-exp (-2*(x-t)))*m t*volterraTerm s m n t
  let B : ℕ → ℝ → ℝ := fun n t => factorialBound s (∫ t, m t) n*‖m t‖
  have he (t : ℝ) : HasSum (fun n => F n t) ((1-exp (-2*(x-t)))*m t*jost s m t) :=
    (jost_summable hm hn hs t).hasSum.mul_left ((1-exp (-2*(x-t)))*m t)
  have hB (t : ℝ) : HasSum (fun n => B n t) (exp (s*(∫ t, m t)/2)*‖m t‖) :=
    (factorialBound_hasSum s (∫ t, m t)).mul_right ‖m t‖
  have hI := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Iic x))
    (F := F) (f := fun t => (1-exp (-2*(x-t)))*m t*jost s m t) B
    (fun n => ((((by fun_prop : Continuous (fun t : ℝ => 1-exp (-2*(x-t))))).aestronglyMeasurable.mul
      hm.aestronglyMeasurable).mul (volterraTerm_properties hm hn hs n).1.aestronglyMeasurable).restrict)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      have hK : ‖1-exp (-2*(x-t))‖ ≤ 1 := by
        rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (exp_le_one_iff.mpr (by
          change t ≤ x at ht
          linarith)))]
        linarith [exp_pos (-2*(x-t))]
      change ‖(1-exp (-2*(x-t)))*m t*volterraTerm s m n t‖ ≤ _
      rw [norm_mul,norm_mul]
      calc
        _ ≤ 1*‖m t‖*factorialBound s (∫ t, m t) n :=
          mul_le_mul (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
            (volterraTerm_global_bound hm hn hs n t) (norm_nonneg _)
            (by positivity)
        _ = B n t := by dsimp [B]; ring)
    (Eventually.of_forall (fun t => (hB t).summable))
    (by
      have heq : (fun t => ∑' n, B n t)=fun t => exp (s*(∫ t, m t)/2)*‖m t‖ :=
        funext (fun t => (hB t).tsum_eq)
      rw [heq]
      exact (hm.norm.const_mul _).integrableOn)
    (Eventually.of_forall he)
  have hshift : HasSum (fun n => volterraTerm s m (n+1) x) (volterra s m (jost s m) x) := by
    have h := hI.mul_left (s/2)
    have hterm (n : ℕ) : s/2*(∫ t in Iic x, F n t)=volterraTerm s m (n+1) x := by
      have hfn : Integrable (fun t => m t*volterraTerm s m n t) :=
        bounded_forcing_integrable hm (volterraTerm_properties hm hn hs n).1.aestronglyMeasurable
          (volterraTerm_global_bound hm hn hs n)
      exact (volterra_integral hfn s x).symm
    rw [show s/2*(∫ t in Iic x, (1-exp (-2*(x-t)))*m t*jost s m t)=
      volterra s m (jost s m) x from (volterra_integral (jost_forcing_integrable hm hn hs) s x).symm] at h
    simpa only [hterm] using h
  have ht := (hasSum_nat_add_iff (f := fun n => volterraTerm s m n x) 1).mp hshift
  have h0 : volterraTerm s m 0 x=1 := rfl
  simp only [Finset.sum_range_one,h0] at ht
  have hz := ht.unique (jost_summable hm hn hs x).hasSum
  dsimp only [jost]
  linarith

end
end «2610.05164v2».Filters
