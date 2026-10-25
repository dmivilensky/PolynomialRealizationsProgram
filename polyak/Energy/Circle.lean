import polyak.Energy.Kernel

/-!
Article: Appendix A, Lemma energy, extension of the symbol inequality.
Use: a real quadratic kernel's even symbol is controlled by frequencies in [0,π].
Proof: choose a representative in [-π,π) and reflect its negative half.
-/

namespace polyak.Energy
noncomputable section

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Article: the full Fourier-circle symbol bound.
Use: the strict certificate on the cosine interval controls every Fourier frequency. -/
theorem kernelSymbol_le_of_halfCircle (K : Kernel) (ε : ℝ)
    (h : ∀ ω : ℝ, 0 ≤ ω → ω ≤ Real.pi →
      kernelSymbol K (ω : FrequencyCircle) ≤ -ε) :
    ∀ θ : FrequencyCircle, kernelSymbol K θ ≤ -ε := by
  intro θ
  let a := AddCircle.equivIco (2*Real.pi) (-Real.pi) θ
  have ha : -Real.pi ≤ (a : ℝ) ∧ (a : ℝ) < -Real.pi+2*Real.pi := a.property
  have he : ((a : ℝ) : FrequencyCircle) = θ := AddCircle.coe_equivIco
  by_cases hpos : 0 ≤ (a : ℝ)
  · rw [← he]
    exact h a hpos (by linarith [ha.2])
  · have hn := h (-(a : ℝ)) (by linarith) (by linarith [ha.1])
    change kernelSymbol K (-((a : ℝ) : FrequencyCircle)) ≤ -ε at hn
    rw [kernelSymbol_neg, he] at hn
    exact hn

end
end polyak.Energy
