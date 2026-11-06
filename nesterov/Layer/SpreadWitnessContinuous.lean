import nesterov.Layer.SpreadWitnessBounds
import nesterov.Layer.SpreadWitnessEnvelope

/-! Continuous global representatives of the actual polar data on one band. -/
namespace nesterov.TwoStep.Spread
noncomputable section
open Set Spectral Phase

theorem frequency_arccos (c : Frequency) : frequency (Real.arccos c)=c := by
  apply Subtype.ext
  exact Real.cos_arccos c.2.1 c.2.2

theorem exists_continuous_polar (a : SymbolPair) {lo hi : ℝ} (hlohi : lo≤hi)
    (hg : ∀ ω∈Icc lo hi,0<g a (frequency ω)) :
    ∃ R Θ : C(Frequency,ℝ), (∀ c : Frequency,0<R c) ∧
      ∀ c : Frequency, Real.arccos c∈Icc lo hi →
        R c=magnitude (g a c) (skew a c) ∧ Θ c=angle (g a c) (skew a c) := by
  let fR : ℝ→ℝ := fun ω=>magnitude (g a (frequency ω)) (skew a (frequency ω))
  let fΘ : ℝ→ℝ := fun ω=>angle (g a (frequency ω)) (skew a (frequency ω))
  have hR : ContinuousOn fR (Icc lo hi) := (continuous_magnitude a).continuousOn
  have hΘ : ContinuousOn fΘ (Icc lo hi) := continuousOn_phase a hg
  let R := nesterov.Spread.extendBand hlohi fR hR
  let Θ := nesterov.Spread.extendBand hlohi fΘ hΘ
  refine ⟨R,Θ,?_,?_⟩
  · intro c
    exact nesterov.Spread.extendBand_positive hlohi fR hR (fun ω hω=>
      magnitude_pos (Or.inl (hg ω hω).ne')) c
  · intro c hc
    have hr := nesterov.Spread.extendBand_eq hlohi fR hR hc
    have ht := nesterov.Spread.extendBand_eq hlohi fΘ hΘ hc
    simp only [fR,fΘ,frequency_arccos] at hr ht
    exact ⟨hr,ht⟩

theorem continuous_polar_eq {a : SymbolPair} {lo hi : ℝ} {R Θ : C(Frequency,ℝ)}
    (hagree : ∀ c : Frequency,Real.arccos c∈Icc lo hi →
      R c=magnitude (g a c) (skew a c) ∧ Θ c=angle (g a c) (skew a c))
    {c : Frequency} (hc : Real.arccos c∈Icc lo hi) :
    (g a c:ℂ)-2*Complex.I*skew a c=(R c:ℂ)*Complex.exp (-(Θ c:ℂ)*Complex.I) := by
  rw [(hagree c hc).1,(hagree c hc).2]
  exact polar_representation _ _

end
end nesterov.TwoStep.Spread
