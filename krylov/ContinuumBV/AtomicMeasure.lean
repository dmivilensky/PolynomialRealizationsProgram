import krylov.ContinuumBV.ActualAtoms
import krylov.Strings.TypeDensity
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
Article: main_krylov, apC:lem:fund, actual singular/atomic decomposition.
Use: split the true singular mass into its continuous singular restriction and
all singleton atoms. Countability is derived from the actual Stieltjes measure.
Source: Lebesgue decomposition, nullity of countable sets and mathlib's exact
Bochner integral over a countable set.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings

def massAtomSet (M : Mass) : Set ℝ := {x | 0 < M.measure {x}}

theorem massAtomSet_countable (M : Mass) : (massAtomSet M).Countable :=
  countable_actual_atoms M

/-- The actual singular-continuous component removes every atom, including
the distinguished initial atom. Physical formulas subsequently restrict to (0,L]. -/
def continuousSingularMass (M : Mass) : Measure ℝ :=
  (M.measure.singularPart volume).restrict (massAtomSet M)ᶜ

theorem singularPart_singleton (M : Mass) (x : ℝ) :
    M.measure.singularPart volume {x} = M.measure {x} := by
  have he := congrArg (fun μ : Measure ℝ ↦ μ {x}) M.type_mass_decomposition
  have hac := withDensity_absolutelyContinuous volume
    (fun t ↦ ENNReal.ofReal (M.typeDensity t ^ 2))
  have hzero := hac (by simp : volume ({x} : Set ℝ) = 0)
  simpa only [Measure.add_apply, hzero, zero_add] using he

/-- The continuous singular component really has no singleton atoms. -/
theorem continuousSingularMass_singleton (M : Mass) (x : ℝ) :
    continuousSingularMass M {x} = 0 := by
  rw [continuousSingularMass, Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ massAtomSet M
  · have he : ({x} : Set ℝ) ∩ (massAtomSet M)ᶜ = ∅ := by simp [hx]
    rw [he, measure_empty]
  · have he : ({x} : Set ℝ) ∩ (massAtomSet M)ᶜ = {x} := by simp [hx]
    rw [he, singularPart_singleton]
    exact le_antisymm (not_lt.mp hx) bot_le

theorem continuousSingularMass_mutuallySingular (M : Mass) :
    continuousSingularMass M ⟂ₘ volume :=
  (Measure.mutuallySingular_singularPart M.measure volume).restrict _

/-- Every atom belongs entirely to the actual singular component, on all
measurable sets simultaneously. No extra discrete measure is introduced. -/
theorem singularPart_restrict_atoms (M : Mass) :
    (M.measure.singularPart volume).restrict (massAtomSet M) =
      M.measure.restrict (massAtomSet M) := by
  have hcount := massAtomSet_countable M
  have hvol : volume (massAtomSet M) = 0 := hcount.measure_zero volume
  have hac := withDensity_absolutelyContinuous volume
    (fun t ↦ ENNReal.ofReal (M.typeDensity t ^ 2))
  have hzero : (volume.withDensity (fun t ↦ ENNReal.ofReal (M.typeDensity t ^ 2))).restrict
      (massAtomSet M) = 0 := Measure.restrict_eq_zero.mpr (hac hvol)
  have he := congrArg (fun μ : Measure ℝ ↦ μ.restrict (massAtomSet M)) M.type_mass_decomposition
  simpa only [Measure.restrict_add, hzero, zero_add] using he

/-- The full singular mass is exactly its continuous part plus all actual atoms. -/
theorem singularPart_eq_continuous_add_atoms (M : Mass) :
    M.measure.singularPart volume = continuousSingularMass M +
      M.measure.restrict (massAtomSet M) := by
  rw [← singularPart_restrict_atoms, continuousSingularMass, add_comm]
  exact ((M.measure.singularPart volume).restrict_add_restrict_compl
    (massAtomSet_countable M).measurableSet).symm

/-- An integrable scalar coefficient over the actual atoms equals the full
countable sum of singleton contributions, with no chosen enumeration. -/
theorem integral_mass_atoms (M : Mass) {f : ℝ → ℝ}
    (hf : IntegrableOn f (massAtomSet M) M.measure) :
    ∫ x in massAtomSet M, f x ∂M.measure =
      ∑' x : massAtomSet M, M.measure.real {(x : ℝ)} * f x := by
  simpa only [smul_eq_mul] using setIntegral_countable f (massAtomSet_countable M) hf

end
end krylov.ContinuumBV
