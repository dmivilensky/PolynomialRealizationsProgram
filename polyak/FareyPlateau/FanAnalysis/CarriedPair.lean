import polyak.Levels.Program.AtomicProgram
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! The arbitrary finite-measure interpretation of a two-point carrier.
The weights are the actual singleton masses; all signed lag inequalities,
including the identically zero lag, follow from the full program. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels MeasureTheory Set
open scoped BigOperators

def pairWeight (μ : Measure Frequency) (a c : Frequency) : Fin 2→NNReal :=
  ![(μ {a}).toNNReal,(μ {c}).toNNReal]
def pairFrequencies (a c : Frequency) : Fin 2→Frequency := ![a,c]

theorem carried_pair_eq {μ : Measure Frequency} [IsFiniteMeasure μ] {a c : Frequency}
    (hne : a≠c) (hcar : ∀ᵐ x ∂μ,x=a ∨ x=c) :
    μ=atomicMeasure (pairWeight μ a c) (pairFrequencies a c) := by
  have he := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac hne).mp hcar
  simpa only [atomicMeasure,pairWeight,pairFrequencies,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,ENNReal.coe_toNNReal (measure_ne_top _ _)] using he

theorem pairWeight_sum_pos {μ : Measure Frequency} [IsFiniteMeasure μ] {a c : Frequency}
    (hne : a≠c) (hcar : ∀ᵐ x ∂μ,x=a ∨ x=c) (hμ : μ≠0) :
    0<∑i,pairWeight μ a c i := by
  have he := carried_pair_eq hne hcar
  by_contra hn
  have hz : ∑i,pairWeight μ a c i=0 := le_antisymm (le_of_not_gt hn) zero_le
  have hpoint : ∀i,pairWeight μ a c i=0 := by
    intro i
    have hh := Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j∈Finset.univ)=>zero_le (a:=pairWeight μ a c j))
    exact hh.mp hz i (Finset.mem_univ i)
  apply hμ
  rw [he]
  simp only [atomicMeasure,hpoint,ENNReal.coe_zero,zero_smul,Finset.sum_const_zero]

theorem pair_solution_inequalities {Θ : Curve} {μ : Measure Frequency} {a c : Frequency}
    (hne : a≠c) (hcar : ∀ᵐ x ∂μ,x=a ∨ x=c) (hμ : ProgramSolution Θ nonzeroLags μ) :
    let w := pairWeight μ a c
    0<∑i,w i ∧
      0≤(w 0:ℝ)*Θ.minimizer a+(w 1:ℝ)*Θ.minimizer c ∧
      ∀n : ℤ,0≤(w 0:ℝ)*Θ.lag n a+(w 1:ℝ)*Θ.lag n c := by
  let : IsFiniteMeasure μ := hμ.1
  have he := carried_pair_eq hne hcar
  refine ⟨pairWeight_sum_pos hne hcar hμ.2.1,?_,?_⟩
  · have hh := hμ.2.2.1
    rw [he,atomicMeasure_integral] at hh
    simpa only [Fin.sum_univ_two,pairFrequencies,Matrix.cons_val_zero,Matrix.cons_val_one] using hh
  · intro n
    by_cases hn : n=0
    · subst n
      simp only [Curve.lag_zero,mul_zero,add_zero,le_refl]
    · have hh := hμ.2.2.2 n hn
      rw [he,atomicMeasure_integral] at hh
      simpa only [Fin.sum_univ_two,pairFrequencies,Matrix.cons_val_zero,Matrix.cons_val_one] using hh

theorem pair_supported_iff (Θ : Curve) (a c : Frequency) (hne : a≠c) :
    (∃μ : Measure Frequency,ProgramSolution Θ nonzeroLags μ ∧ (∀ᵐ x ∂μ,x=a ∨ x=c)) ↔
      ∃u v : NNReal,0<u+v ∧ ProgramSolution Θ nonzeroLags (atomicMeasure ![u,v] ![a,c]) := by
  constructor
  · rintro ⟨μ,hμ,hcar⟩
    let : IsFiniteMeasure μ := hμ.1
    refine ⟨(μ {a}).toNNReal,(μ {c}).toNNReal,?_,?_⟩
    · simpa only [pairWeight,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using
        pairWeight_sum_pos hne hcar hμ.2.1
    · change ProgramSolution Θ nonzeroLags (atomicMeasure (pairWeight μ a c) (pairFrequencies a c))
      rw [←carried_pair_eq hne hcar]
      exact hμ
  · rintro ⟨u,v,_huv,hμ⟩
    refine ⟨_,hμ,?_⟩
    unfold atomicMeasure
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    fin_cases i <;> simp

end polyak.FareyPlateau.FanAnalysis
