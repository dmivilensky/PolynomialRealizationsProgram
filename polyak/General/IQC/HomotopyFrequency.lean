import polyak.General.IQC.FourierConvolution
import polyak.General.IQC.BoundedLoop

/-! Appendix D, Lemma homotopy in its frequency-domain form.
The bounded IQC is built from the measurable frequency matrix. The actual
causal l1 filter is diagonalized by canonical zero-extension/Fourier;
the frequency inequality is integrated to obtain the time graph gap before
the proved causal finite-continuation engine is invoked. -/
noncomputable section
namespace polyak.General.IQC
open MeasureTheory Filter Set
open scoped ENNReal
namespace Feedback
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩
open Fourier

/-- The complete scalar frequency-domain homotopy theorem, including actual
causal execution and a single bound for every tau and every l2 forcing. -/
theorem homotopy_frequency_uniform_bound (F : Feedback ℂ) {h : ℕ→ℝ}
    (hh : Summable (fun n=>|h n|)) (hF : ∀ x,F.plant x=convolution h x)
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {ε : ℝ} (hε : 0<ε)
    (hgap : ∀ᵐ ω ∂circleMeasure,
      matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (transfer h ω)≤ -ε)
    (hpos : ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ x : SequenceSpace ℂ,
      0≤∫ ω,pointValue (scalarIQC P) ω (halfLineTransform x ω)
        (halfLineTransform (τ • F.deltaL2 x) ω) ∂circleMeasure) :
    ∃ C : ℝ,0<C ∧ ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ f : ℕ→ℂ,SquareSummable f→
      SquareSummable (F.run τ f) ∧ sequenceNorm (F.run τ f)≤C*sequenceNorm f := by
  let B := bilinearIQC halfLineTransform (scalarIQC P)
  have hn (z : SequenceSpace ℂ) : iqcValue B (F.plantL2 z) z≤ -ε*‖z‖^2 :=
    graph_gap_of_transform halfLineTransform (scalarIQC P) (scalarOperator (transfer h))
      F.plantL2 (halfLine_plant_transform F hh hF) (scalar_frequency_gap P (transfer h) hgap) z
  have hp (τ : ℝ) (hτ : τ∈Icc (0:ℝ) 1) (x : SequenceSpace ℂ) :
      0≤ iqcValue B x (τ • F.deltaL2 x) := by
    rw [iqcValue_eq_integral]
    exact hpos τ hτ x
  refine ⟨aprioriConstant ‖B‖ F.gain ε,aprioriConstant_pos (norm_nonneg B) F.gain_nonneg hε,?_⟩
  intro τ hτ f hf
  exact F.iqc_uniform_bound B le_rfl hε hn hp hτ f hf

end Feedback
end polyak.General.IQC
