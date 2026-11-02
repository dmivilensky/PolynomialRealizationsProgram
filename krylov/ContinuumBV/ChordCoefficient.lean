import krylov.ContinuumBV.ChainPartitions
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: main_krylov, apC:lem:fund, nonlinear jumps.
Use: replace a first-order coefficient by its exact average along a finite
state chord. The average has the exact finite potential increment and remains
bounded on compact C¹ domains, including chords spanning large jumps.
Source: the ordinary fundamental theorem of calculus and dominated convergence.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact average of the Fréchet derivative on a finite state chord. -/
def chordCoefficient (F : E → ℝ) (u v : E) : E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ F (AffineMap.lineMap u v t)

/-- A zero-length chord has exactly the ordinary Fréchet coefficient. -/
theorem chordCoefficient_self (F : E → ℝ) (u : E) :
    chordCoefficient F u u = fderiv ℝ F u := by
  simp [chordCoefficient]

/-- C¹ regularity on the actual chord makes its derivative average integrable. -/
theorem chord_derivative_continuousOn {F : E → ℝ} {u v : E}
    (hF : ∀ w ∈ segment ℝ u v, ContDiffAt ℝ 1 F w) :
    ContinuousOn (fun t : ℝ => fderiv ℝ F (AffineMap.lineMap u v t)) (Icc 0 1) := by
  intro t ht
  exact (((hF _ (lineMap_mem_segment ℝ u v ht)).continuousAt_fderiv (by norm_num)).comp
    (AffineMap.hasDerivAt_lineMap (a := u) (b := v) (x := t)).continuousAt).continuousWithinAt

/-- The averaged coefficient gives the exact nonlinear jump, not its linear
approximation. No smallness of the chord or atom is required. -/
theorem chordCoefficient_apply_sub {F : E → ℝ} {u v : E}
    (hF : ∀ w ∈ segment ℝ u v, ContDiffAt ℝ 1 F w) :
    chordCoefficient F u v (v - u) = F v - F u := by
  have hi : IntervalIntegrable (fun t : ℝ => fderiv ℝ F (AffineMap.lineMap u v t)) volume 0 1 :=
    (chord_derivative_continuousOn hF).intervalIntegrable_of_Icc (by norm_num)
  rw [chordCoefficient, ContinuousLinearMap.intervalIntegral_apply hi]
  have hc : ContinuousOn (fun t : ℝ => (fderiv ℝ F (AffineMap.lineMap u v t)) (v - u)) (Icc 0 1) :=
    (ContinuousLinearMap.apply ℝ ℝ (v - u)).continuous.comp_continuousOn
      (chord_derivative_continuousOn hF)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (f := fun t => F (AffineMap.lineMap u v t)) (fun t ht =>
      ((hF _ (lineMap_mem_segment ℝ u v (by simpa using ht))).differentiableAt
        (by norm_num)).hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap)
    (hc.intervalIntegrable_of_Icc (by norm_num))
  simpa using he

/-- A uniform derivative bound on the whole chord bounds its exact average. -/
theorem norm_chordCoefficient_le {F : E → ℝ} {u v : E} {C : ℝ}
    (hC : ∀ w ∈ segment ℝ u v, ‖fderiv ℝ F w‖ ≤ C) :
    ‖chordCoefficient F u v‖ ≤ C := by
  simpa [chordCoefficient] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (fun t ht => hC _
      (lineMap_mem_segment ℝ u v (Ioc_subset_Icc_self (by simpa using ht))))

/-- Exact chord averages converge when both endpoints converge, under a
genuine uniform derivative bound. This is ordinary dominated convergence on
the chord parameter, and permits a nonzero limiting jump. -/
theorem tendsto_chordCoefficient {F : E → ℝ} {u v : ℕ → E} {a b : E}
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (hF : ∀ n w, w ∈ segment ℝ (u n) (v n) → ContDiffAt ℝ 1 F w)
    (hFab : ∀ w ∈ segment ℝ a b, ContDiffAt ℝ 1 F w)
    (hbound : ∃ C, ∀ n w, w ∈ segment ℝ (u n) (v n) → ‖fderiv ℝ F w‖ ≤ C) :
    Tendsto (fun n => chordCoefficient F (u n) (v n)) atTop (𝓝 (chordCoefficient F a b)) := by
  obtain ⟨C, hC⟩ := hbound
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => fderiv ℝ F (AffineMap.lineMap (u n) (v n) t))
      (volume.restrict (Ioc 0 1)) := by
    intro n
    exact ((chord_derivative_continuousOn (hF n)).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  have hl : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), Tendsto
      (fun n => fderiv ℝ F (AffineMap.lineMap (u n) (v n) t)) atTop
        (𝓝 (fderiv ℝ F (AffineMap.lineMap a b t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hline : Tendsto (fun n => AffineMap.lineMap (u n) (v n) t) atTop
        (𝓝 (AffineMap.lineMap a b t)) := by
      simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] using
        ((hv.sub hu).const_smul t).add hu
    exact ((hFab _ (lineMap_mem_segment ℝ a b (Ioc_subset_Icc_self ht))).continuousAt_fderiv
      (by norm_num)).tendsto.comp hline
  have he := tendsto_integral_filter_of_norm_le_const
    (Eventually.of_forall hmeas)
    (⟨C, Eventually.of_forall fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hC n _ (lineMap_mem_segment ℝ (u n) (v n) (Ioc_subset_Icc_self ht))⟩) hl
  simpa only [chordCoefficient, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using he

end
end krylov.ContinuumBV
