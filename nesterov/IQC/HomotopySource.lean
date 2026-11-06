import nesterov.IQC.CausalMultiplierNorm

/-!
Article: Lemma `homotopy`, with its original quantifier order. One constant
is chosen before the spatial dimension, causal nonlinear operator, homotopy
parameter and forcing. Its only inputs are the scalar convolution gain,
the uniform matrix multiplier bound and the strict frequency gap.
-/
namespace nesterov.IQC
noncomputable section
open Set MeasureTheory polyak.General.IQC polyak.General.IQC.Fourier
open scoped BigOperators ENNReal
local instance : Fact (0<2*Real.pi):=⟨Real.two_pi_pos⟩

/-- The literal source homotopy theorem. Stable strictly proper scalar
rational plants are covered by their absolutely summable causal impulse;
the result also holds for every such scalar convolution. -/
theorem homotopy (h : ℕ→ℝ) (hh : Summable (fun n=>|h n|)) (h0 : h 0=0)
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {M ε : ℝ}
    (hP : ∀ i j,‖P i j‖≤M) (hε : 0<ε)
    (hgap : ∀ᵐ ω ∂circleMeasure,
      matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (transfer h ω)≤ -ε) :
    ∃ C : ℝ,0<C ∧ ∀ (d : ℕ)
      (δ : (ℕ→EuclideanSpace ℝ (Fin d))→ℕ→EuclideanSpace ℝ (Fin d))
      (hc : Causal δ) (hn : ∀ x N,prefixNorm (δ x) N≤prefixNorm x N),
      let F:=CausalFeedback.ofConvolution h hh h0 δ hc hn
      (∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
        0≤∑ i : Fin d,∫ ω,pointValue (scalarIQC P) ω
          (halfLineTransform (coordinateSignal i x) ω)
          (halfLineTransform (coordinateSignal i (τ • F.deltaL2 x)) ω) ∂circleMeasure) →
      ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ f : ℕ→EuclideanSpace ℝ (Fin d),SquareSummable f→
        ∃! x : ℕ→EuclideanSpace ℝ (Fin d),
          x=convolution h (τ • δ x)+f ∧ SquareSummable x ∧ sequenceNorm x≤C*sequenceNorm f := by
  let C:=aprioriConstant (8*M) (∑' n,|h n|) ε
  have hM : 0≤M:=(norm_nonneg (P 0 0)).trans (hP 0 0)
  refine ⟨C,aprioriConstant_pos (by positivity) (tsum_nonneg (fun n=>abs_nonneg (h n))) hε,?_⟩
  intro d δ hc hn
  dsimp only
  let F:=CausalFeedback.ofConvolution h hh h0 δ hc hn
  intro hpos τ hτ f hf
  have he:=F.frequency_uniform_bound_of_norm_bound hh (fun _=>rfl) P hP hε hgap hpos hτ f hf
  refine ⟨F.run τ f,⟨F.run_equation τ f,he.1,he.2⟩,?_⟩
  intro x hx
  exact F.eq_run_of_equation τ f x hx.1

end
end nesterov.IQC
