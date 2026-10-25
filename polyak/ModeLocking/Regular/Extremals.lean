import polyak.ModeLocking.Regular.Slackness

/-! Complementarity and support localization for every genuine measure,
including every relaxation containing the regular certificate's lags. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels MeasureTheory
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def certificate : CertificateSymbol (Geometry.shiftedCurve q s) (D.lags : Set ℤ) where
  lags := D.lags
  lags_subset := by simp
  weight := D.dual
  weight_nonneg n hn := (D.dual_pos n hn).le
  gamma := 0
  gamma_nonneg := le_rfl

theorem certificate_total : Global.Symbols.total D.certificate = 1 := by
  simp only [Global.Symbols.total, certificate, add_zero, D.dual_sum]

def dualWeights : Global.Symbols.Weights (D.lags : Set ℤ) :=
  Global.Symbols.normalizeWeights D.certificate (by rw [D.certificate_total]; norm_num)

theorem dualWeights_eval (ω : Frequency) : D.dualWeights.eval (Geometry.shiftedCurve q s) ω =
    finiteSymbol q s D.lags D.dual ω := by
  rw [dualWeights, Global.Symbols.normalizeWeights_eval, D.certificate_total, div_one]
  rw [finiteSymbol_actual]
  simp only [CertificateSymbol.eval, certificate, zero_mul, add_zero]

theorem symbol_zero_iff (ω : Frequency) : finiteSymbol q s D.lags D.dual ω = 0 ↔
    ω = frequencyZero ∨ ∃ i, ω = D.atoms i := by
  constructor
  · intro hz
    by_cases h0 : ω = frequencyZero
    · exact Or.inl h0
    right
    by_contra hn
    have hx : 0 < (ω : ℝ) := by
      apply lt_of_le_of_ne ω.property.1
      intro he
      exact h0 (Subtype.ext he.symm)
    have hs := D.dual_strict ω hx ω.property.2 (fun i hi => hn ⟨i, Subtype.ext hi⟩)
    rw [hz] at hs
    exact lt_irrefl _ hs
  · rintro (rfl | ⟨i, rfl⟩)
    · exact D.symbol_zero_endpoint
    · exact D.symbol_zero_support i

theorem program_carried {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N')
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) N' w) :
    ∀ᵐ ω ∂w, ω = frequencyZero ∨ ∃ i, ω = D.atoms i := by
  have hzero := D.dualWeights.solution_carried_zero
    (fun ω => by rw [D.dualWeights_eval]; exact D.symbol_nonpos ω ω.property)
    (hw.relax hN)
  filter_upwards [hzero] with ω hω
  rw [D.dualWeights_eval] at hω
  exact (D.symbol_zero_iff ω).mp hω

theorem program_tight {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N')
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) N' w)
    (n : ℤ) (hn : n ∈ D.lags) : ∫ ω, (Geometry.shiftedCurve q s).lag n ω ∂w = 0 := by
  apply (D.dualWeights.complementary_slackness
    (fun ω => by rw [D.dualWeights_eval]; exact D.symbol_nonpos ω ω.property)
    (hw.relax hN)).1 n
  change 0 < Global.Symbols.normalizedWeight D.certificate n
  unfold Global.Symbols.normalizedWeight
  change 0 < if n ∈ D.lags then D.dual n / Global.Symbols.total D.certificate else 0
  rw [ite_eq_left hn, D.certificate_total, div_one]
  exact D.dual_pos n hn

end polyak.ModeLocking.RegularData
