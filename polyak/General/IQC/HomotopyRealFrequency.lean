import polyak.General.IQC.FourierCoordinates

/-! Appendix D, Lemma homotopy on the article's original real spatial
signals. Each real coordinate is embedded into the canonical complex
Fourier space. The nonlinear operator and its causal execution remain on
R^d throughout. -/
noncomputable section
namespace polyak.General.IQC
open MeasureTheory Filter Set
open scoped ENNReal
namespace Fourier
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Project both real signals into one complex Fourier coordinate. -/
def coordinatePair {d : ℕ} (i : Fin d) :
    (SequenceSpace (EuclideanSpace ℝ (Fin d))×SequenceSpace (EuclideanSpace ℝ (Fin d)))→L[ℝ]
      (SequenceSpace ℂ×SequenceSpace ℂ) :=
  (coordinateCLM i).prodMap (coordinateCLM i)

/-- The literal blockwise frequency IQC defines a bounded real bilinear
form on the original finite-dimensional real signal space. -/
def realBilinearIQC (d : ℕ) (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) :
    BilinearIQC (SequenceSpace (EuclideanSpace ℝ (Fin d))) :=
  ∑ i : Fin d,(bilinearIQC halfLineTransform (scalarIQC P)).bilinearComp
    (coordinatePair i) (coordinatePair i)

theorem realBilinearIQC_value {d : ℕ} (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure)
    (x y : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    iqcValue (realBilinearIQC d P) x y=
      ∑ i,iqcValue (bilinearIQC halfLineTransform (scalarIQC P))
        (coordinateSignal i x) (coordinateSignal i y) := by
  simp only [iqcValue,realBilinearIQC,sum_apply,
    ContinuousLinearMap.bilinearComp_apply]
  rfl

theorem realBilinearIQC_integral {d : ℕ} (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure)
    (x y : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    iqcValue (realBilinearIQC d P) x y=
      ∑ i,∫ ω,pointValue (scalarIQC P) ω
        (halfLineTransform (coordinateSignal i x) ω)
        (halfLineTransform (coordinateSignal i y) ω) ∂circleMeasure := by
  rw [realBilinearIQC_value]
  apply Finset.sum_congr rfl
  intro i _
  exact iqcValue_eq_integral _ _ _ _

/-- Real coordinate projection commutes with the actual scalar causal filter. -/
theorem coordinate_convolution {d : ℕ} (h : ℕ→ℝ)
    (x : ℕ→EuclideanSpace ℝ (Fin d)) (i : Fin d) (n : ℕ) :
    ((convolution h x n) i : ℂ)=convolution h (fun n=>(x n i:ℂ)) n := by
  simp only [convolution,LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_sum,Finset.sum_apply,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [PiLp.smul_apply,Complex.ofReal_mul,Complex.real_smul,smul_eq_mul]
  congr 1
  simp only [delay]
  split <;> simp_all

/-- Actual real-vector convolution is transformed coordinate by coordinate;
no complex extension of the nonlinear operator is introduced. -/
theorem coordinate_plant_transform {d : ℕ}
    (F : Feedback (EuclideanSpace ℝ (Fin d))) {h : ℕ→ℝ}
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

end Fourier
namespace Feedback
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩
open Fourier

/-- The source's stable strictly causal scalar convolution and causal
nonexpansive nonlinear map assemble the actual feedback system directly. -/
def ofConvolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℕ→ℝ) (hh : Summable (fun n=>|h n|)) (h0 : h 0=0)
    (δ : (ℕ→E)→ℕ→E) (hc : Causal δ) (hz : δ 0=0)
    (hn : ∀ x y N,prefixNorm (δ x-δ y) N≤prefixNorm (x-y) N) : Feedback E where
  plant := convolution h
  strictlyCausal := convolution_strictCausal h0
  gain := ∑' n,|h n|
  gain_nonneg := tsum_nonneg (fun n=>abs_nonneg (h n))
  prefix_gain := convolution_prefix_gain hh
  delta := δ
  delta_causal := hc
  delta_zero := hz
  delta_nonexpansive := hn

/-- Every sequence solving the causal feedback equation is the constructed
execution, without assuming that the sequence is square summable. -/
theorem eq_run_of_equation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Feedback E) (τ : ℝ) (f x : ℕ→E)
    (hx : x=F.plant (τ • F.delta x)+f) : x=F.run τ f := by
  apply causalSolve_unique (F.loop_strictCausal τ) f x
  intro k
  exact congrFun hx k

/-- The generic frequency-domain homotopy theorem. The transfer identity
identifies the actual plant's bounded frequency multiplier. The strict time
graph inequality is proved from the frequency inequality, rather than being
an assumption. No rationality or impulse-response summability is needed. -/
theorem homotopy_real_frequency_bound_of_transform {d : ℕ}
    (F : Feedback (EuclideanSpace ℝ (Fin d))) (g : Lp ℂ ∞ circleMeasure)
    (htransform : ∀ (i : Fin d) (x : SequenceSpace (EuclideanSpace ℝ (Fin d))),
      halfLineTransform (coordinateSignal i (F.plantL2 x))=
        multiply (scalarOperator g) (halfLineTransform (coordinateSignal i x)))
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {ε : ℝ} (hε : 0<ε)
    (hgap : ∀ᵐ ω ∂circleMeasure,
      matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (g ω)≤ -ε)
    (hpos : ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
      0≤∑ i : Fin d,∫ ω,pointValue (scalarIQC P) ω
        (halfLineTransform (coordinateSignal i x) ω)
        (halfLineTransform (coordinateSignal i (τ • F.deltaL2 x)) ω) ∂circleMeasure) :
    ∃ C : ℝ,0<C ∧ ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→
      ∀ f : ℕ→EuclideanSpace ℝ (Fin d),SquareSummable f→
      SquareSummable (F.run τ f) ∧ sequenceNorm (F.run τ f)≤C*sequenceNorm f := by
  let B := realBilinearIQC d P
  have hn (z : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
      iqcValue B (F.plantL2 z) z≤ -ε*‖z‖^2 := by
    rw [realBilinearIQC_value]
    calc
      _≤∑ i : Fin d,-ε*‖coordinateSignal i z‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact graph_gap_of_pair halfLineTransform (scalarIQC P) (scalarOperator g)
          (scalar_frequency_gap P g hgap)
          (coordinateSignal i (F.plantL2 z)) (coordinateSignal i z)
          (htransform i z)
      _= -ε*‖z‖^2 := by rw [← Finset.mul_sum,sum_coordinate_norm_sq]
  have hp (τ : ℝ) (hτ : τ∈Icc (0:ℝ) 1)
      (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
      0≤ iqcValue B x (τ • F.deltaL2 x) := by
    rw [realBilinearIQC_integral]
    exact hpos τ hτ x
  refine ⟨aprioriConstant ‖B‖ F.gain ε,aprioriConstant_pos (norm_nonneg B) F.gain_nonneg hε,?_⟩
  intro τ hτ f hf
  exact F.iqc_uniform_bound B le_rfl hε hn hp hτ f hf

/-- Every actual stable causal scalar filter satisfies the generic transfer
identity: this corollary proves it from the summable impulse response, for
the article's original real signals and nonlinear operator. -/
theorem homotopy_real_frequency_uniform_bound {d : ℕ}
    (F : Feedback (EuclideanSpace ℝ (Fin d))) {h : ℕ→ℝ}
    (hh : Summable (fun n=>|h n|)) (hF : ∀ x,F.plant x=convolution h x)
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {ε : ℝ} (hε : 0<ε)
    (hgap : ∀ᵐ ω ∂circleMeasure,
      matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (transfer h ω)≤ -ε)
    (hpos : ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
      0≤∑ i : Fin d,∫ ω,pointValue (scalarIQC P) ω
        (halfLineTransform (coordinateSignal i x) ω)
        (halfLineTransform (coordinateSignal i (τ • F.deltaL2 x)) ω) ∂circleMeasure) :
    ∃ C : ℝ,0<C ∧ ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→
      ∀ f : ℕ→EuclideanSpace ℝ (Fin d),SquareSummable f→
      SquareSummable (F.run τ f) ∧ sequenceNorm (F.run τ f)≤C*sequenceNorm f :=
  homotopy_real_frequency_bound_of_transform F (transfer h)
    (coordinate_plant_transform F hh hF) P hε hgap hpos

end Feedback
end polyak.General.IQC
