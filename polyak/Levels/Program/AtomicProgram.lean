import polyak.Levels.Program.Periodic
import polyak.Waves.Finite

/-! The literal finite linear program in the original, unnormalized weights. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels
variable {J : Type*} [Fintype J]

def atomicMeasure (w : J→NNReal) (a : J→Frequency) : Measure Frequency:=
  ∑j,(w j:ENNReal)•Measure.dirac (a j)

instance finite_atomicMeasure (w : J→NNReal) (a : J→Frequency) :
    IsFiniteMeasure (atomicMeasure w a) := by
  constructor
  simp only [atomicMeasure,Measure.coe_finsetSum,Finset.sum_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _=>ENNReal.coe_lt_top)

theorem atomicMeasure_integral (w : J→NNReal) (a : J→Frequency) (f : Frequency→ℝ) :
    (∫ω,f ω ∂atomicMeasure w a)=∑j,(w j:ℝ)*f (a j) := by
  have hi (j:J) : Integrable f ((w j:ENNReal)•Measure.dirac (a j)):=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  simpa [atomicMeasure,integral_smul_measure,NNReal.smul_def,smul_eq_mul] using
    (integral_finsetSum_measure (s:=Finset.univ) (fun j _=>hi j))

theorem atomicMeasure_ne_zero (w : J→NNReal) (a : J→Frequency)
    (hw : 0<∑j,w j) : atomicMeasure w a≠0 := by
  intro hz
  have hu:=congrArg (fun μ:Measure Frequency=>μ Set.univ) hz
  have he : (∑j,w j:NNReal)=0 := by
    apply ENNReal.coe_injective
    simpa [atomicMeasure,←ENNReal.ofNNReal_finsetSum] using hu
  exact (ne_of_gt hw) he

theorem atomicMeasure_carried_grid (w : J→NNReal) (a : J→Frequency) (k : ℕ)
    (ha : ∀j,a j∈periodicGrid k) : ∀ᵐω ∂atomicMeasure w a,ω∈periodicGrid k := by
  unfold atomicMeasure
  rw [ae_finsetSum_measure_iff]
  intro j _
  exact Measure.ae_smul_measure (by simpa using ha j) _

theorem atomic_program_iff (Θ : Curve) {k : ℕ} (hk : 0<k)
    (w : J→NNReal) (a : J→Frequency) (hw : 0<∑j,w j)
    (ha : ∀j,a j∈periodicGrid k) :
    ProgramSolution Θ nonzeroLags (atomicMeasure w a) ↔
      0≤∑j,(w j:ℝ)*Θ.minimizer (a j) ∧
        ∀n : ℕ,0<n→n<k→0≤∑j,(w j:ℝ)*Θ.lag (n:ℤ) (a j) := by
  have hc:=atomicMeasure_carried_grid w a k ha
  calc
    ProgramSolution Θ nonzeroLags (atomicMeasure w a) ↔
      ProgramSolution Θ nonzeroLags (atomicMeasure w a) ∧ (∀ᵐω ∂atomicMeasure w a,ω∈periodicGrid k) :=
        ⟨fun h=>⟨h,hc⟩,And.left⟩
    _ ↔ _ := by
      rw [←periodicSolution_iff hk]
      simp only [PeriodicSolution,atomicMeasure_integral]
      exact ⟨fun h=>⟨h.2.2.2.1,h.2.2.2.2⟩,
        fun h=>⟨inferInstance,atomicMeasure_ne_zero w a hw,hc,h.1,h.2⟩⟩

/-- Removing precisely the zero weights preserves the entire measure. -/
theorem atomicMeasure_trim (w : J→NNReal) (a : J→Frequency) :
    atomicMeasure (fun j:{j // 0<w j}=>w j.val) (fun j=>a j.val)=atomicMeasure w a := by
  classical
  unfold atomicMeasure
  rw [←Finset.sum_subtype (Finset.univ.filter (fun j=>0<w j)) (by simp)
    (fun j=>(w j:ENNReal)•Measure.dirac (a j))]
  apply Finset.sum_filter_of_ne
  intro j _ hne
  by_contra hn
  have hz : w j=0:=le_antisymm (le_of_not_gt hn) zero_le
  exact hne (by simp [hz])

theorem sum_trim_weights (w : J→NNReal) :
    (∑j:{j // 0<w j},w j.val)=∑j,w j := by
  classical
  rw [←Finset.sum_subtype (Finset.univ.filter (fun j=>0<w j)) (by simp) w]
  apply Finset.sum_filter_of_ne
  intro j _ hne
  exact lt_of_le_of_ne zero_le (Ne.symm hne)

end polyak.Levels
