import polyak.ModeLocking.Localization.Endpoints
import polyak.ModeLocking.Localization.ThresholdSymbol

/-! The exact heavy-atom localization inequality, with the factor two. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem atom_localization (q : General.Tuning) (s t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ)
    (hnorm : (∑ i, a i)+γ=1) (hst : t ≤ s)
    (hT : ∀ ω, symbol q t n a γ ω ≤ 0)
    {w : Measure Frequency} [IsFiniteMeasure w]
    (hfeas : 0 ≤ ∫ ω, symbol q s n a γ ω ∂w)
    (x : Frequency) (hx : x ∈ Threshold.interiorCarrier) (hw : 0 < w.real {x}) :
    -symbol q t n a γ x ≤ (2*(s-t)*w.real univ / w.real {x}) *
      (Real.sin (Geometry.shiftedCurve q t x) / Real.sin (Geometry.shiftedCurve q s x)) := by
  have hb := atom_defect_bound q s t n a γ ha hγ hnorm hst hT hfeas x
  have hrs := sineRatio_pos q s t x
  have hden := mul_pos hw hrs
  have he : (2*(s-t)*w.real univ / w.real {x}) *
      (Real.sin (Geometry.shiftedCurve q t x) / Real.sin (Geometry.shiftedCurve q s x)) =
      (2*(s-t)*w.real univ) / (w.real {x} * sineRatio q s t x) := by
    rw [sineRatio_interior q s t x hx]
    field_simp [(phase_sin_pos q s x hx).ne', (phase_sin_pos q t x hx).ne']
  rw [he]
  apply (le_div_iff₀ hden).mpr
  unfold defect at hb
  nlinarith only [hb]

theorem local_for_program (q : General.Tuning) (N : Finset ℤ)
    (a : {n // n ∈ N} → ℝ) (γ s t : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ)
    (hT : ∀ ω, symbol q t (fun i => i.val) a γ ω ≤ 0)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) N w) :
    (∫ ω in Threshold.interiorCarrier,
      defect q s t (fun i => i.val) a γ ω ∂w) + γ*w.real {frequencyZero} +
      |symbol q s (fun i => i.val) a γ frequencyPi| * w.real {frequencyPi} ≤
    (s-t)*(∫ ω in Threshold.interiorCarrier, budget q s (fun i => i.val) a γ ω ∂w) := by
  have : IsFiniteMeasure w := hw.1
  have hf : 0 ≤ ∫ ω, symbol q s (fun i : {n // n ∈ N} => i.val) a γ ω ∂w :=
    integral_symbol_nonneg q s (fun i : {n // n ∈ N} => i.val) a γ ha hγ hw.2.2.1
      (fun i => hw.2.2.2 i.val i.property)
  exact localization_with_endpoints q s t (fun i : {n // n ∈ N} => i.val) a γ hT hf

end polyak.ModeLocking.Localization
