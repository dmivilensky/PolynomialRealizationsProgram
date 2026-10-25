import polyak.Levels.Lattice.Residues
import polyak.Levels.Program.Definitions

/-! Single rational atoms solve the actual full program precisely at the
sharp phase threshold. The minimizer constraint and theta=pi are included. -/
noncomputable section
namespace polyak.Levels.Lattice
open MeasureTheory Set

theorem dirac_program_iff (Θ : Curve) (𝒩 : Set ℤ) (ω : Frequency) :
    ProgramSolution Θ 𝒩 (Measure.dirac ω) ↔
      0≤Θ.minimizer ω ∧ ∀ n∈𝒩,0≤Θ.lag n ω := by
  simp only [ProgramSolution,integral_dirac]
  constructor
  · intro h
    exact ⟨h.2.2.1,h.2.2.2⟩
  · intro h
    exact ⟨inferInstance,Measure.dirac_ne_zero,h.1,h.2⟩

/-- Farey's single-atom conclusion, for every genuine curve. -/
theorem rational_atom_program_iff (Θ : Curve) {j k : ℕ} (hjk : j.Coprime k)
    (hk : 2≤k) (ω : Frequency) (hω : (ω:ℝ)=2*Real.pi*j/k) :
    ProgramSolution Θ nonzeroLags (Measure.dirac ω) ↔ Θ ω≤Real.pi/k := by
  rw [dirac_program_iff]
  have hphase : (∀ n : ℤ,0≤Θ.lag n ω) ↔ Θ ω≤Real.pi/k := by
    simp only [Curve.lag,hω,sub_nonneg]
    exact General.Regions.primitive_phase_criterion hjk hk (Θ.pos ω).le (Θ.le_pi ω)
  constructor
  · rintro ⟨_,h⟩
    apply hphase.mp
    intro n
    by_cases hn : n=0
    · simp only [hn,Curve.lag_zero,le_refl]
    · exact h n hn
  · intro h
    refine ⟨?_,fun n _=>hphase.mpr h n⟩
    have hkR : (2:ℝ)≤k := by exact_mod_cast hk
    have hk0 : (0:ℝ)<k := by positivity
    have hdiv : Real.pi/k≤Real.pi/2 :=
      (div_le_div_iff₀ hk0 (by norm_num : (0:ℝ)<2)).mpr (by nlinarith [Real.pi_pos])
    have hh : Θ ω≤Real.pi/2 := h.trans hdiv
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Θ.pos ω],hh⟩

/-- The corresponding full-program feasibility is witnessed by the
specified atom, rather than by an unrelated spectrum. -/
theorem rational_atom_feasible (Θ : Curve) {j k : ℕ} (hjk : j.Coprime k)
    (hk : 2≤k) (ω : Frequency) (hω : (ω:ℝ)=2*Real.pi*j/k)
    (hθ : Θ ω≤Real.pi/k) : FP Θ :=
  ⟨Measure.dirac ω,(rational_atom_program_iff Θ hjk hk ω hω).mpr hθ⟩

/-- Along a rational ray, the phase bound is exactly being at or beyond
the primitive lattice point. -/
theorem rational_ray_scale {j k : ℕ} (hk : 0<k) {θ : ℝ} (hθ : 0<θ) :
    xi (2*Real.pi*j/k) θ=(Real.pi/((k:ℝ)*θ))*j ∧
    eta θ=(Real.pi/((k:ℝ)*θ))*k := by
  constructor
  · unfold xi
    field_simp
  · unfold eta
    field_simp

theorem rational_ray_beyond_iff {k : ℕ} (hk : 0<k) {θ : ℝ} (hθ : 0<θ) :
    (k:ℝ)≤eta θ ↔ θ≤Real.pi/k := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  unfold eta
  rw [le_div_iff₀ hθ,le_div_iff₀ hkR]
  constructor <;> intro h <;> nlinarith

end polyak.Levels.Lattice
