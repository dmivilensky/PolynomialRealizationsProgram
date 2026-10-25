import polyak.Levels.Program.Normalization
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Endpoint atoms, and more generally all phase-pi atoms, can be removed. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

theorem integral_restrict_compl_ge {w : Measure Frequency} [IsFiniteMeasure w]
    {Z : Set Frequency} (hZ : MeasurableSet Z) {f : Frequency→ℝ} (hf : Integrable f w)
    (hbad : ∀ω∈Z,f ω≤0) : (∫ ω,f ω ∂w)≤∫ ω in Zᶜ,f ω ∂w := by
  have hz : (∫ ω in Z,f ω ∂w)≤0 := integral_nonpos_of_ae
    ((ae_restrict_mem hZ).mono (fun ω hω => hbad ω hω))
  have he := integral_add_compl hZ hf
  linarith

theorem ProgramSolution.remove_bad {Θ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) {Z : Set Frequency} (hZ : MeasurableSet Z)
    (hmin : ∀ω∈Z,Θ.minimizer ω=-1) (hlag : ∀n∈𝒩,∀ω∈Z,Θ.lag n ω≤0) :
    ProgramSolution Θ 𝒩 (w.restrict Zᶜ) := by
  have : IsFiniteMeasure w := h.1
  refine ⟨inferInstance,?_,?_,?_⟩
  · intro hz
    have : NeZero w := ⟨h.2.1⟩
    have hz' : w Zᶜ=0 := by
      have he := congrArg (fun μ : Measure Frequency => μ Set.univ) hz
      simpa using he
    have hae : ∀ᵐω∂w,ω∈Z := by
      rw [ae_iff]
      exact hz'
    have he : (∫ ω,Θ.minimizer ω ∂w)=∫ _ : Frequency,(-1:ℝ) ∂w :=
      integral_congr_ae (hae.mono fun ω hω => hmin ω hω)
    rw [integral_const] at he
    have hp := measureReal_univ_pos (μ:=w)
    simp only [smul_eq_mul,mul_neg,mul_one] at he
    linarith [h.2.2.1]
  · exact h.2.2.1.trans (integral_restrict_compl_ge hZ
      (integrable_curve_minimizer Θ w) (fun ω hω => by rw [hmin ω hω]; norm_num))
  · intro n hn
    exact (h.2.2.2 n hn).trans (integral_restrict_compl_ge hZ
      (integrable_curve_lag Θ n w) (hlag n hn))

theorem ProgramSolution.remove_pi_phase {Θ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) :
    ProgramSolution Θ 𝒩 (w.restrict {ω | Θ ω≠Real.pi}) := by
  have hZ : MeasurableSet {ω | Θ ω=Real.pi} :=
    (isClosed_eq Θ.continuous continuous_const).measurableSet
  apply h.remove_bad hZ
  · intro ω hω
    change Θ ω=Real.pi at hω
    simp only [Curve.minimizer,hω,Real.cos_pi]
  · intro n _ ω hω
    rw [Curve.lag_expand,hω,Real.cos_pi,Real.sin_pi]
    nlinarith [Real.cos_le_one ((n:ℝ)*(ω:ℝ))]

theorem ProgramSolution.remove_endpoints {Θ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) :
    ProgramSolution Θ 𝒩 (w.restrict {ω | 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi}) := by
  let Z : Set Frequency := {frequencyZero,frequencyPi}
  have hZ : MeasurableSet Z := (measurableSet_singleton frequencyPi).insert frequencyZero
  have he : Zᶜ={ω : Frequency | 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi} := by
    ext ω
    simp only [Z,Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_ofPred_eq,
      not_or]
    have h0 : ω=frequencyZero ↔ (ω:ℝ)=0 := by constructor <;> intro hh <;> [simp [hh,frequencyZero]; exact Subtype.ext hh]
    have hp : ω=frequencyPi ↔ (ω:ℝ)=Real.pi := by constructor <;> intro hh <;> [simp [hh,frequencyPi]; exact Subtype.ext hh]
    rw [h0,hp]
    constructor
    · rintro ⟨h0,hp⟩
      exact ⟨lt_of_le_of_ne ω.property.1 (Ne.symm h0),lt_of_le_of_ne ω.property.2 hp⟩
    · rintro ⟨h0,hp⟩
      exact ⟨ne_of_gt h0,ne_of_lt hp⟩
  rw [← he]
  apply h.remove_bad hZ
  · intro ω hω
    rcases hω with rfl | hω
    · exact Θ.minimizer_at_zero
    · rw [Set.mem_singleton_iff] at hω
      rw [hω,Θ.minimizer_at_pi]
  · intro n _ ω hω
    rcases hω with rfl | hω
    · rw [Θ.lag_at_zero]
    · rw [Set.mem_singleton_iff] at hω
      rw [hω]
      exact Θ.lag_at_pi_nonpos n

end polyak.Levels
