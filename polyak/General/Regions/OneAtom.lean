import polyak.General.Parameters
import polyak.Realization.Rate

/-! Exact one-atom feasibility and its original-rate realization. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics Spectral

/-- A single unit-weight frequency in the exact finite-spectrum representation. -/
def oneAtom (c : Frequency) : Spectrum :=
  Waves.finiteSpectrum (fun _ : Fin 1=>1) (fun _=>c) (by simp)

/-- The one-atom moment equations retain all lower and upper lag inequalities. -/
theorem oneAtom_feasible_iff (c : Frequency) (m : C(Frequency,ℂ)) (C t : ℝ) :
    Waves.MixtureFeasible (oneAtom c) m C t ↔
      |C|≤1-Complex.normSq (m c) ∧ ∀ n : ℕ,1≤n →
      0≤(1-Complex.normSq (m c))*(Real.cosh (n*t)-Real.cos (n*Real.arccos c))-
        2*(m c).im*Real.sin (n*Real.arccos c)+C*Real.sinh (n*t) ∧
      0≤(1-Complex.normSq (m c))*(Real.cosh (n*t)-Real.cos (n*Real.arccos c))+
        2*(m c).im*Real.sin (n*Real.arccos c)-C*Real.sinh (n*t) := by
  simp only [Waves.MixtureFeasible,oneAtom,Waves.spectrumG,Waves.spectrumA,Waves.spectrumB,
    Waves.finiteSpectrum_integral,Fin.sum_univ_one,NNReal.coe_one,one_mul]

/-- Any feasible atom gives the actual original lower rate; positivity is needed only for t>0. -/
theorem oneAtom_exp_le_originalRate (q : Tuning) (c : Frequency) {C t : ℝ}
    (h : Waves.MixtureFeasible (oneAtom c)
      (Waves.multiplierMap q.A q.B q.beta t) C t)
    (hstrict : 0<t→|C|<1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta t c)) :
    Real.exp t≤rate q.x q.y 1 q.beta := by
  have hA : normalizedA q.x q.y 1 q.beta=q.A := by dsimp [normalizedA,Tuning.A]; ring
  have hB : normalizedB q.x q.y 1=q.B := by dsimp [normalizedB,Tuning.B]; ring
  apply Realization.exp_le_originalRate q.x_pos q.x_lt_y (by norm_num) q.beta_nonneg
    q.beta_lt_one (by simpa using q.y_lt) (fun _ : Fin 1=>1) (fun _=>c) (by simp)
  · simpa only [hA,hB,oneAtom] using h
  · intro ht
    simpa only [hA,hB,Waves.spectrumG,Waves.finiteSpectrum_integral,Fin.sum_univ_one,
      NNReal.coe_one,one_mul] using hstrict ht

end
end polyak.General.Regions
