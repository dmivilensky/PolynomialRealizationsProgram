import polyak.Levels.Program.Definitions

/-! Article: the periodic frequency grids Ω_k and programs P_k.
The zero endpoint is excluded and the endpoint pi is retained for even k.
Carriage is an almost-everywhere statement for the actual finite measure. -/

noncomputable section
open MeasureTheory
namespace polyak.Levels

def periodicGrid (k : ℕ) : Set Frequency :=
  {ω | 0<(ω:ℝ) ∧ ∃ j : ℤ,(k:ℝ)*(ω:ℝ)=(j:ℝ)*(2*Real.pi)}

def PeriodicFP (Θ : Curve) (k : ℕ) : Prop :=
  ∃ w : Measure Frequency,ProgramSolution Θ nonzeroLags w ∧ ∀ᵐ ω ∂w,ω∈periodicGrid k

theorem PeriodicFP.fp {Θ : Curve} {k : ℕ} (h : PeriodicFP Θ k) : FP Θ := by
  rcases h with ⟨w,hw,_⟩
  exact ⟨w,hw⟩

theorem mem_periodicGrid_iff {k : ℕ} (hk : 0<k) (ω : Frequency) :
    ω∈periodicGrid k ↔ ∃ j : ℤ,0<j ∧ 2*j≤k ∧ (ω:ℝ)=2*Real.pi*j/k := by
  have hkR : 0<(k:ℝ) := by exact_mod_cast hk
  constructor
  · rintro ⟨hω,j,hj⟩
    have hjR : 0<(j:ℝ) := by nlinarith [mul_pos hkR hω,Real.pi_pos]
    have hjkR : (2:ℝ)*j≤k := by nlinarith [ω.property.2,Real.pi_pos]
    refine ⟨j,by exact_mod_cast hjR,by exact_mod_cast hjkR,?_⟩
    apply (eq_div_iff hkR.ne').mpr
    nlinarith [hj]
  · rintro ⟨j,hj,hjk,hω⟩
    have hjR : 0<(j:ℝ) := by exact_mod_cast hj
    refine ⟨by rw [hω]; positivity,j,?_⟩
    rw [hω]
    field_simp

end polyak.Levels
