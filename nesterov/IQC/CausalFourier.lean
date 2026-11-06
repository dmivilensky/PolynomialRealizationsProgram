import nesterov.IQC.CausalHomotopy
import polyak.General.IQC.HomotopyRealFrequency

/-! The source Fourier homotopy theorem with only causal gain-bounded feedback. -/
namespace nesterov.IQC
noncomputable section
open Set MeasureTheory polyak.General.IQC polyak.General.IQC.Fourier
open scoped BigOperators ENNReal
local instance : Fact (0<2*Real.pi):=⟨Real.two_pi_pos⟩

private theorem coordinatePair_sq_sum_le {d : ℕ}
    (X : SequenceSpace (EuclideanSpace ℝ (Fin d))×SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    (∑ i : Fin d,‖coordinatePair i X‖^2)≤2*‖X‖^2 := by
  have he : (∑ i : Fin d,‖coordinatePair i X‖^2)≤
      (∑ i : Fin d,‖coordinateSignal i X.1‖^2)+∑ i : Fin d,‖coordinateSignal i X.2‖^2 := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    change (max ‖coordinateSignal i X.1‖ ‖coordinateSignal i X.2‖)^2≤_
    rcases le_total ‖coordinateSignal i X.1‖ ‖coordinateSignal i X.2‖ with h|h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ‖coordinateSignal i X.1‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ‖coordinateSignal i X.2‖]
  rw [sum_coordinate_norm_sq,sum_coordinate_norm_sq] at he
  have hx : ‖X.1‖≤‖X‖:=le_max_left _ _
  have hy : ‖X.2‖≤‖X‖:=le_max_right _ _
  nlinarith [norm_nonneg X.1,norm_nonneg X.2,norm_nonneg X]

/-- One scalar Fourier IQC norm bounds every real spatial dimension. -/
theorem realBilinearIQC_norm_le (d : ℕ) (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) :
    ‖realBilinearIQC d P‖≤2*‖bilinearIQC halfLineTransform (scalarIQC P)‖ := by
  let B:=bilinearIQC halfLineTransform (scalarIQC P)
  apply (realBilinearIQC d P).opNorm_le_bound (by positivity)
  intro X
  apply ((realBilinearIQC d P) X).opNorm_le_bound (by positivity)
  intro Y
  rw [Real.norm_eq_abs]
  have hc:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun i=>‖coordinatePair i X‖) (fun i=>‖coordinatePair i Y‖)
  have hp : (∑ i : Fin d,‖coordinatePair i X‖^2)*(∑ i : Fin d,‖coordinatePair i Y‖^2)≤
      (2*‖X‖^2)*(2*‖Y‖^2) :=
    mul_le_mul (coordinatePair_sq_sum_le X) (coordinatePair_sq_sum_le Y)
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (by positivity)
  have hsum : (∑ i : Fin d,‖coordinatePair i X‖*‖coordinatePair i Y‖)≤2*‖X‖*‖Y‖ := by
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))) (by positivity)).mp
    nlinarith [hc.trans hp]
  simp only [realBilinearIQC,sum_apply,ContinuousLinearMap.bilinearComp_apply]
  change |∑ i : Fin d,B (coordinatePair i X) (coordinatePair i Y)|≤_
  calc
    _≤∑ i : Fin d,|B (coordinatePair i X) (coordinatePair i Y)|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑ i : Fin d,‖B‖*‖coordinatePair i X‖*‖coordinatePair i Y‖:=
      Finset.sum_le_sum (fun i _=>bounded_bilinear_abs B _ _)
    _=‖B‖*(∑ i : Fin d,‖coordinatePair i X‖*‖coordinatePair i Y‖):=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
    _≤‖B‖*(2*‖X‖*‖Y‖):=mul_le_mul_of_nonneg_left hsum (norm_nonneg B)
    _=_:=by ring

namespace CausalFeedback

/-- An actual stable strictly proper scalar convolution and any causal
nonlinear map with the source's gain-from-zero bound. -/
def ofConvolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℕ→ℝ) (hh : Summable (fun n=>|h n|)) (h0 : h 0=0)
    (δ : (ℕ→E)→ℕ→E) (hc : Causal δ)
    (hn : ∀ x N,prefixNorm (δ x) N≤prefixNorm x N) : CausalFeedback E where
  plant:=convolution h
  strictlyCausal:=convolution_strictCausal h0
  gain:=∑' n,|h n|
  gain_nonneg:=tsum_nonneg (fun n=>abs_nonneg (h n))
  prefix_gain:=convolution_prefix_gain hh
  delta:=δ
  delta_causal:=hc
  delta_prefix_bound:=hn

theorem coordinate_plant_transform {d : ℕ}
    (F : CausalFeedback (EuclideanSpace ℝ (Fin d))) {h : ℕ→ℝ}
    (hh : Summable (fun n=>|h n|)) (hF : ∀ x,F.plant x=convolution h x)
    (i : Fin d) (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    halfLineTransform (coordinateSignal i (F.plantL2 x))=
      multiply (scalarOperator (transfer h)) (halfLineTransform (coordinateSignal i x)) := by
  have he : zeroExtendL2 (coordinateSignal i (F.plantL2 x))=
      wholeConvolution h (zeroExtendL2 (coordinateSignal i x)) := by
    ext k
    rw [zeroExtend_convolution hh]
    change zeroExtend (fun n=>(F.plant x n i:ℂ)) k=
      zeroExtend (convolution h (fun n=>(x n i:ℂ))) k
    rw [hF]
    congr 1
    funext n
    exact coordinate_convolution h (fun n=>x n) i n
  change scalarUnitary (zeroExtendL2 (coordinateSignal i (F.plantL2 x)))=_
  rw [he,wholeConvolution_transform hh]
  rfl

/-- A dimension-independent scalar constant for the literal source IQC. -/
def frequencyConstant (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) (gain ε : ℝ) : ℝ:=
  aprioriConstant (2*‖bilinearIQC halfLineTransform (scalarIQC P)‖) gain ε

/-- Lemma homotopy: the actual source frequency graph inequality gives
square summability and one gain, with no incremental assumption on Δ. The
same displayed constant works for every spatial dimension and every Δ. -/
theorem frequency_uniform_bound {d : ℕ}
    (F : CausalFeedback (EuclideanSpace ℝ (Fin d))) {h : ℕ→ℝ}
    (hh : Summable (fun n=>|h n|)) (hF : ∀ x,F.plant x=convolution h x)
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {ε : ℝ} (hε : 0<ε)
    (hgap : ∀ᵐ ω ∂circleMeasure,
      matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (transfer h ω)≤ -ε)
    (hpos : ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
      0≤∑ i : Fin d,∫ ω,pointValue (scalarIQC P) ω
        (halfLineTransform (coordinateSignal i x) ω)
        (halfLineTransform (coordinateSignal i (τ • F.deltaL2 x)) ω) ∂circleMeasure)
    {τ : ℝ} (hτ : τ∈Icc (0:ℝ) 1) (f : ℕ→EuclideanSpace ℝ (Fin d)) (hf : SquareSummable f) :
    SquareSummable (F.run τ f) ∧
      sequenceNorm (F.run τ f)≤frequencyConstant P F.gain ε*sequenceNorm f := by
  let B:=realBilinearIQC d P
  have hn (z : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
      iqcValue B (F.plantL2 z) z≤ -ε*‖z‖^2 := by
    rw [realBilinearIQC_value]
    calc
      _≤∑ i : Fin d,-ε*‖coordinateSignal i z‖^2:=by
        apply Finset.sum_le_sum
        intro i _
        exact graph_gap_of_pair halfLineTransform (scalarIQC P) (scalarOperator (transfer h))
          (scalar_frequency_gap P (transfer h) hgap)
          (coordinateSignal i (F.plantL2 z)) (coordinateSignal i z)
          (F.coordinate_plant_transform hh hF i z)
      _= -ε*‖z‖^2:=by rw [←Finset.mul_sum,sum_coordinate_norm_sq]
  have hp (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
      0 ≤ iqcValue B x (s • F.deltaL2 x) := by
    rw [realBilinearIQC_integral]
    exact hpos s hs x
  exact F.iqc_uniform_bound B (realBilinearIQC_norm_le d P) hε hn hp hτ f hf

end CausalFeedback
end
end nesterov.IQC
