import nesterov.IQC.StationaryFilters
import polyak.General.IQC.PlantGap

/-!
The genuine nonlinear causal feedback for an arbitrary stationary method.
The strict graph gap is proved from the finite polynomial certificate on the
full latent signal. All constants are independent of the spatial Hilbert space.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC polyak.General.IQC polyak.Energy
variable (M : nesterov.StationaryMethod)

/-- Scalar plant gain supplied by the actual absolutely summable impulse. -/
def queryGainL2 (μ L t : ℝ) : ℝ:=∑' n,|M.queryImpulse μ L t n|

theorem queryGainL2_nonneg (μ L t : ℝ) : 0≤M.queryGainL2 μ L t:=tsum_nonneg (fun _=>abs_nonneg _)

/-- The finite denominator filter converts the latent gap into an input gap. -/
def polynomialGap {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) : ℝ:=
  cert.ε/(1+(filterSize (M.normalizedFilter μ L t))^2)

theorem polynomialGap_pos {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) : 0<M.polynomialGap cert:=
  div_pos cert.ε_pos (by positivity)

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual stable strictly causal query plant and actual discounted gradient. -/
def feedback {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) : Feedback E:=
  Feedback.ofConvolution (M.queryImpulse μ L t) (M.queryImpulse_summable hμL hstable)
    (M.queryImpulse_zero μ L t) (scaledGradient ψ t) (scaledGradient_causal ψ t)
    (scaledGradient_zero hψ t) (scaledGradient_nonexpansive hψ t)

@[simp] theorem feedback_plant {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) :
    (M.feedback hμL hstable hψ).plant=convolution (M.queryImpulse μ L t):=rfl

/-- The polynomial certificate proves the strict IQC graph inequality for the
actual plant, including every zero and common factor of u and p. -/
theorem feedback_strict_graph {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) (z : SequenceSpace E) :
    iqcValue (halfLineCertificate (transported cert))
      ((M.feedback hμL hstable hψ).plantL2 z) z≤ -M.polynomialGap cert*‖z‖^2 := by
  let latent : ℕ→E:=M.zeroLatent μ L t (fun n=>z n)
  have hlatent : SquareSummable latent := by
    have he : latent=convolution (M.latentImpulse μ L t) (fun n=>z n):=
      funext (M.zeroLatent_convolution μ L t _)
    rw [he]
    exact convolution_squareSummable (M.latentImpulse_summable hμL hstable) (lp_squareSummable z)
  let w : ZSpace E:=zeroExtendL2 (toL2 latent hlatent)
  have hq : filterCLM (M.queryFilter t) w=
      zeroExtendL2 ((M.feedback hμL hstable hψ).plantL2 z) := by
    apply Subtype.ext
    funext k
    rw [filterCLM_apply]
    exact M.zeroLatent_whole_query μ L t (fun n=>z n) k
  have hp : filterCLM (M.normalizedFilter μ L t) w=zeroExtendL2 z := by
    apply Subtype.ext
    funext k
    rw [filterCLM_apply]
    exact M.zeroLatent_whole_normalized hμL t (fun n=>z n) k
  have hg:=M.normalizedFilter_strict_graph cert w
  rw [hq,hp] at hg
  have hnorm:=filterCLM_bound (M.normalizedFilter μ L t) w
  rw [hp,zeroExtendL2_norm] at hnorm
  have hc:=input_gap (norm_nonneg z) (norm_nonneg w)
    (filterSize_nonneg (M.normalizedFilter μ L t)) cert.ε_pos hnorm
  change certificateForm (transported cert)
    (zeroExtendL2 ((M.feedback hμL hstable hψ).plantL2 z),zeroExtendL2 z)
    (zeroExtendL2 ((M.feedback hμL hstable hψ).plantL2 z),zeroExtendL2 z)≤_
  exact hg.trans (by dsimp [polynomialGap]; nlinarith only [hc])

end Hilbert

/-- One explicit gain works for every spatial Hilbert space and potential. -/
def feedbackConstant {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) : ℝ:=
  aprioriConstant (certificateNormBound (transported cert)) (M.queryGainL2 μ L t)
    (M.polynomialGap cert)

theorem feedbackConstant_pos {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) : 0<M.feedbackConstant cert:=
  aprioriConstant_pos (certificateNormBound_nonneg _) (M.queryGainL2_nonneg μ L t)
    (M.polynomialGap_pos cert)

/-- Lemma homotopy for the actual finite-memory stationary query plant.
Square summability is a conclusion about the unrestricted causal solution. -/
theorem feedback_uniform_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t)
    {τ : ℝ} (hτ : τ∈Set.Icc (0:ℝ) 1) (f : ℕ→E) (hf : SquareSummable f) :
    SquareSummable ((M.feedback hμL hstable hψ).run τ f) ∧
      sequenceNorm ((M.feedback hμL hstable hψ).run τ f)≤M.feedbackConstant cert*sequenceNorm f := by
  let _ : NormedSpace ℝ ((SequenceSpace E×SequenceSpace E) →L[ℝ] ℝ):=inferInstance
  let _ : SeminormedAddCommGroup ((SequenceSpace E×SequenceSpace E) →L[ℝ] ℝ):=inferInstance
  let F:=M.feedback hμL hstable hψ
  let B:=halfLineCertificate (E:=E) (transported cert)
  have hn : ‖B‖≤certificateNormBound (transported cert):=
    (halfLineCertificate_norm_le _).trans (certificateForm_norm_le _)
  have hneg (z : SequenceSpace E) : iqcValue B (F.plantL2 z) z≤ -M.polynomialGap cert*‖z‖^2:=
    M.feedback_strict_graph hμL hstable hψ cert z
  have hpos (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) (x : SequenceSpace E) :
      0 ≤ iqcValue B x (s • F.deltaL2 x):=
    halfLine_homotopy_IQC cert hψ hs x
  exact F.iqc_uniform_bound B hn (M.polynomialGap_pos cert) hneg hpos hτ f hf

end
end nesterov.StationaryMethod
