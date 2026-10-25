import polyak.ModeLocking.Boundary.Definitions
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! A moving atom of uniformly positive mass survives weak convergence.
The diagonal in the product space turns the moving singleton into a fixed closed set. -/
noncomputable section
namespace polyak.ModeLocking
open Levels MeasureTheory Set Filter
open scoped Topology ENNReal

theorem isClosed_probability_mass_ge {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {A : Set X} (hA : IsClosed A) (m : ℝ≥0∞) :
    IsClosed {ν : ProbabilityMeasure X | m ≤ (ν : Measure X) A} := by
  apply isClosed_iff_forall_filter.mpr
  intro ν F hF hmem hlim
  let _ : F.NeBot := hF
  have hev : ∀ᶠ μ : ProbabilityMeasure X in F,m ≤ (μ : Measure X) A := hmem (by simp)
  have hleft : m ≤ F.limsup (fun μ : ProbabilityMeasure X => (μ : Measure X) A) := by
    simpa only [limsup_const] using Filter.limsup_le_limsup hev
  exact hleft.trans (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hA)

theorem probability_prod_diagonal (ν : ProbabilityMeasure Frequency) (x : Frequency) :
    (ν.prod (diracProba x) : Measure (Frequency × Frequency)) {p | p.1=p.2} =
      (ν : Measure Frequency) {x} := by
  change (ν : Measure Frequency).prod (Measure.dirac x) {p | p.1=p.2} = _
  rw [Measure.prod_dirac,Measure.map_apply measurable_prodMk_right
    (isClosed_eq continuous_fst continuous_snd).measurableSet]
  congr 1

theorem isClosed_moving_atom (m : ℝ≥0∞) :
    IsClosed {p : ProbabilityMeasure Frequency × Frequency |
      m ≤ (p.1 : Measure Frequency) {p.2}} := by
  have hd : IsClosed {p : Frequency × Frequency | p.1=p.2} :=
    isClosed_eq continuous_fst continuous_snd
  have hc : Continuous (fun p : ProbabilityMeasure Frequency × Frequency =>
      p.1.prod (diracProba p.2)) :=
    ProbabilityMeasure.continuous_prod.comp
      (continuous_fst.prodMk (continuous_diracProba.comp continuous_snd))
  have hh := (isClosed_probability_mass_ge hd m).preimage hc
  change IsClosed {p : ProbabilityMeasure Frequency × Frequency |
    m ≤ (p.1.prod (diracProba p.2) : Measure (Frequency × Frequency)) {a | a.1=a.2}} at hh
  simpa only [probability_prod_diagonal] using hh

theorem isClosed_moving_atom_real (m : ℝ) :
    IsClosed {p : ProbabilityMeasure Frequency × Frequency |
      m ≤ (p.1 : Measure Frequency).real {p.2}} := by
  have he (p : ProbabilityMeasure Frequency × Frequency) :
      ENNReal.ofReal m ≤ (p.1 : Measure Frequency) {p.2} ↔
        m ≤ (p.1 : Measure Frequency).real {p.2} := by
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    rfl
  simpa only [he] using isClosed_moving_atom (ENNReal.ofReal m)

end polyak.ModeLocking
