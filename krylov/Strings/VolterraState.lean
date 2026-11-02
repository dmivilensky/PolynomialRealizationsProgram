import krylov.Strings.WindowMass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Article: main_krylov, apC:eq:state.
Use: Identify the continuous Volterra displacement with the first-order string
equation by Fubini against the actual positive measure. The argument permits
atoms, so the cumulative slope uses the closed right endpoint.
Source: mathlib's Bochner Fubini theorem and the measure of real intervals.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace Window

/-- Fubini identifies the integrated cumulative slope with the string Green
kernel. The order condition is non-strict, preserving atoms at each position. -/
theorem integral_cumulative_eq_green {L : ℝ≥0} (ν : Measure (Window L))
    [IsFiniteMeasure ν] (f : C(Window L, ℝ)) (x : Window L) :
    (∫ t in Ioc 0 (x : ℝ), ∫ y, if (y : ℝ) ≤ t then f y else 0 ∂ν) =
      ∫ y, kernel x y * f y ∂ν := by
  have : IsFiniteMeasure (volume.restrict (Ioc 0 (x : ℝ))) := ⟨by simp⟩
  have hi : Integrable (fun z : ℝ × Window L ↦ if (z.2 : ℝ) ≤ z.1 then f z.2 else 0)
      ((volume.restrict (Ioc 0 (x : ℝ))).prod ν) := by
    refine Integrable.of_bound ?_ ‖f‖ ?_
    · apply Measurable.aestronglyMeasurable
      exact Measurable.ite (measurableSet_le
        (measurable_subtype_coe.comp measurable_snd) measurable_fst)
        (f.continuous.measurable.comp measurable_snd) measurable_const
    · filter_upwards with z
      split_ifs
      · exact f.norm_coe_le_norm z.2
      · simp
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with y
  have hf : (fun t : ℝ ↦ if (y : ℝ) ≤ t then f y else 0) =
      (Ici (y : ℝ)).indicator (fun _ ↦ f y) := by
    ext t
    simp only [indicator, mem_Ici]
  rw [hf, setIntegral_indicator measurableSet_Ici]
  by_cases hy : (y : ℝ) = 0
  · have hs : Ioc (0 : ℝ) x ∩ Ici (y : ℝ) = Ioc 0 (x : ℝ) := by
      rw [hy]
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ici]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.1.le⟩⟩
    rw [hs, integral_const]
    simp [Measure.real, kernel, hy, x.property.1]
  · have hyp : 0 < (y : ℝ) := lt_of_le_of_ne y.property.1 (Ne.symm hy)
    have hs : Ioc (0 : ℝ) x ∩ Ici (y : ℝ) = Icc (y : ℝ) x := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · intro h
        exact ⟨h.2, h.1.2⟩
      · intro h
        exact ⟨⟨hyp.trans_le h.1, h.2⟩, h.1⟩
    rw [hs, integral_const]
    simp [Measure.real, kernel, ENNReal.toReal_ofReal']

/-- Exact equality between the integrated first-order equation and the
Green-kernel form, independently of whether the position solves either one. -/
theorem position_integral_eq_free_green {L : ℝ≥0} (ν : Measure (Window L))
    [IsFiniteMeasure ν] (a b : ℝ) (f : C(Window L, ℝ)) (x : Window L) :
    (a + ∫ t in Ioc 0 (x : ℝ),
      (b + ∫ y, if (y : ℝ) ≤ t then f y else 0 ∂ν)) =
      a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν := by
  have hc : IntegrableOn (fun t : ℝ ↦ ∫ y, if (y : ℝ) ≤ t then f y else 0 ∂ν)
      (Ioc 0 (x : ℝ)) := by
    have : IsFiniteMeasure (volume.restrict (Ioc 0 (x : ℝ))) := ⟨by simp⟩
    have hi : Integrable (fun z : ℝ × Window L ↦ if (z.2 : ℝ) ≤ z.1 then f z.2 else 0)
        ((volume.restrict (Ioc 0 (x : ℝ))).prod ν) := by
      refine Integrable.of_bound ?_ ‖f‖ ?_
      · apply Measurable.aestronglyMeasurable
        exact Measurable.ite (measurableSet_le
          (measurable_subtype_coe.comp measurable_snd) measurable_fst)
          (f.continuous.measurable.comp measurable_snd) measurable_const
      · filter_upwards with z
        split_ifs
        · exact f.norm_coe_le_norm z.2
        · simp
    exact hi.integral_prod_left
  rw [integral_add (integrableOn_const (C := b) (by simp)) hc,
    integral_cumulative_eq_green ν f x, integral_const]
  have hv : (volume.restrict (Ioc 0 (x : ℝ))).real univ = (x : ℝ) := by
    simp [Measure.real, ENNReal.toReal_ofReal, x.property.1]
  rw [hv, smul_eq_mul]
  ring

/-- First-order position equation of every finite-window Volterra solution.
The right-hand slope is reconstructed from the actual measure, rather than
supplied as an additional unknown or regularity assumption. -/
theorem volterra_position_integral {L : ℝ≥0} (ν : Measure (Window L))
    [IsFiniteMeasure ν] (a b : ℝ) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν)
    (x : Window L) :
    f x = a + ∫ t in Ioc 0 (x : ℝ),
      (b + ∫ y, if (y : ℝ) ≤ t then f y else 0 ∂ν) := by
  rw [position_integral_eq_free_green, hf x]

end Window
end
end krylov.Strings
