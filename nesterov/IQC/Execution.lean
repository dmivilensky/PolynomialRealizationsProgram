import nesterov.IQC.Feedback
import nesterov.IQC.ResponseBounds
import nesterov.Rates.Envelope
import polyak.General.IQC.UniformEnergy

/-!
A strict polynomial certificate bounds the actual discounted latent execution
in every real Hilbert space. The constants contain only the method,
curvatures, exponent and finite certificate.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC polyak.General.IQC
variable (M : nesterov.StationaryMethod)

def powerMass (μ L t : ℝ) : ℝ:=
  ∑' n,‖companion M.memory (fun j=>(M.realTransitionCoeff μ L t j:ℂ))^n‖
def initialMass (t : ℝ) : ℝ:=∑ j : Fin M.memory,Real.exp (-(j.val:ℝ)*t)
def queryFreeGain (μ L t : ℝ) : ℝ:=
  M.powerMass μ L t*(∑ j,|M.discountedQueryCoeff t j|)*M.initialMass t
def latentFreeGain (μ L t : ℝ) : ℝ:=M.powerMass μ L t*M.initialMass t
def latentGainL2 (μ L t : ℝ) : ℝ:=∑' n,|M.latentImpulse μ L t n|
def executionGain {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) : ℝ:=
  M.latentFreeGain μ L t+M.latentGainL2 μ L t*M.feedbackConstant cert*M.queryFreeGain μ L t

theorem executionGain_nonneg {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t) : 0≤M.executionGain cert := by
  have hp : 0≤M.powerMass μ L t:=tsum_nonneg (fun _=>norm_nonneg _)
  have hi : 0≤M.initialMass t:=Finset.sum_nonneg (fun _ _=>(Real.exp_pos _).le)
  have hl : 0≤M.latentGainL2 μ L t:=tsum_nonneg (fun _=>abs_nonneg _)
  have hq : 0≤∑ j,|M.discountedQueryCoeff t j|:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hc:=(M.feedbackConstant_pos cert).le
  unfold executionGain latentFreeGain queryFreeGain
  positivity

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem discounted_initial_sum (t : ℝ) (w : ℕ→E) :
    (∑ j : Fin M.memory,‖M.discountedHistory t w 0 j‖)≤M.initialMass t*M.stateNorm w 0 := by
  unfold initialMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  simp only [discountedHistory,Nat.zero_add,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [Nat.zero_add] using M.norm_le_stateNorm w 0 j

/-- The actual discounted query has an ℓ² norm controlled by the complete
initial memory state, uniformly over potentials and Hilbert spaces. -/
theorem query_execution_bound {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t)
    (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (M.query w k)) :
    SquareSummable (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • M.query w k) ∧
      sequenceNorm (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • M.query w k)≤
        (M.feedbackConstant cert*M.queryFreeGain μ L t)*M.stateNorm w 0 := by
  let x : ℕ→E:=fun k=>Real.exp (-(k:ℝ)*t) • M.query w k
  let f:=freeObservation (M.realTransitionCoeff μ L t) (M.discountedQueryCoeff t)
    (M.discountedHistory t w 0)
  have hf:=freeObservation_squareSummable_norm (M.realTransitionCoeff μ L t)
    (M.discountedQueryCoeff t) (M.discountedHistory t w 0)
    (M.realTransition_powers_summable hμL hstable)
  have hfn : sequenceNorm f≤M.queryFreeGain μ L t*M.stateNorm w 0 := by
    apply hf.2.trans
    have hq : 0≤M.powerMass μ L t*(∑ j,|M.discountedQueryCoeff t j|):=
      mul_nonneg (tsum_nonneg (fun _=>norm_nonneg _)) (Finset.sum_nonneg (fun _ _=>abs_nonneg _))
    have hh:=mul_le_mul_of_nonneg_left (M.discounted_initial_sum t w) hq
    simpa only [powerMass,queryFreeGain,mul_assoc] using hh
  have hscaled : scaledGradient ψ t x=(fun k : ℕ=>Real.exp (-(k:ℝ)*t) • gradient ψ (M.query w k)) := by
    funext k
    dsimp [scaledGradient,x]
    rw [smul_smul,←Real.exp_add,show (k:ℝ)*t+(-(k:ℝ))*t=0 by ring,
      Real.exp_zero,one_smul]
    simp only [neg_mul]
  have hx : x=(M.feedback hμL hstable hψ).run 1 f := by
    apply Feedback.eq_run_of_equation
    simp only [one_smul,feedback_plant]
    change x=convolution (M.queryImpulse μ L t) (scaledGradient ψ t x)+f
    rw [hscaled]
    funext k
    exact M.query_response hμL t w (fun k=>gradient ψ (M.query w k)) hw k
  have hb:=M.feedback_uniform_bound hμL hstable hψ cert
    (τ:=1) (by constructor <;> norm_num) f hf.1
  rw [←hx] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hh:=mul_le_mul_of_nonneg_left hfn (M.feedbackConstant_pos cert).le
  simpa only [mul_assoc] using hh

/-- The discounted normalized gradients have the same uniform query bound. -/
theorem gradient_execution_bound {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t)
    (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (M.query w k)) :
    SquareSummable (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • gradient ψ (M.query w k)) ∧
      sequenceNorm (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • gradient ψ (M.query w k))≤
        (M.feedbackConstant cert*M.queryFreeGain μ L t)*M.stateNorm w 0 := by
  have hq:=M.query_execution_bound hμL hstable hψ cert w hw
  let x : ℕ→E:=fun k=>Real.exp (-(k:ℝ)*t) • M.query w k
  have he : scaledGradient ψ t x=(fun k : ℕ=>Real.exp (-(k:ℝ)*t) • gradient ψ (M.query w k)) := by
    funext k
    dsimp [scaledGradient,x]
    rw [smul_smul,←Real.exp_add,show (k:ℝ)*t+(-(k:ℝ))*t=0 by ring,
      Real.exp_zero,one_smul]
    simp only [neg_mul]
  have hs:=scaledGradient_squareSummable hψ t hq.1
  refine ⟨by rwa [he] at hs,?_⟩
  have hn : sequenceNorm (scaledGradient ψ t x)≤sequenceNorm x := by
    apply sequenceNorm_le_of_prefix_bound (sequenceNorm_nonneg x)
    intro N
    have hh:=scaledGradient_nonexpansive hψ t x 0 N
    rw [scaledGradient_zero hψ t] at hh
    simp only [sub_zero] at hh
    exact hh.trans (prefixNorm_le_sequenceNorm hq.1 N)
  rw [he] at hn
  exact hn.trans hq.2

/-- The main uniform latent ℓ² estimate for the literal stationary execution. -/
theorem latent_execution_bound {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (cert : nesterov.Duality.StrictCertificate (M.symbolPair μ L t) t)
    (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (M.query w k)) :
    SquareSummable (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • w k) ∧
      sequenceNorm (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • w k)≤M.executionGain cert*M.stateNorm w 0 := by
  let σ : ℕ→E:=fun k=>Real.exp (-(k:ℝ)*t) • gradient ψ (M.query w k)
  let f : ℕ→E:=fun k=>freeState (M.realTransitionCoeff μ L t) (M.discountedHistory t w 0) k M.firstIndex
  have hs:=M.gradient_execution_bound hμL hstable hψ cert w hw
  have hf:=freeState_squareSummable_norm (M.realTransitionCoeff μ L t)
    (M.discountedHistory t w 0) (M.realTransition_powers_summable hμL hstable) M.firstIndex
  have hfn : sequenceNorm f≤M.latentFreeGain μ L t*M.stateNorm w 0 := by
    apply hf.2.trans
    have hpower : 0≤M.powerMass μ L t:=tsum_nonneg (fun _=>norm_nonneg _)
    have hh:=mul_le_mul_of_nonneg_left (M.discounted_initial_sum t w) hpower
    simpa only [powerMass,latentFreeGain,mul_assoc] using hh
  have hc:=convolution_squareSummable (M.latentImpulse_summable hμL hstable) hs.1
  have hcn:=convolution_sequenceNorm (M.latentImpulse_summable hμL hstable) hs.1
  have he : (fun k : ℕ=>Real.exp (-(k:ℝ)*t) • w k)=f+convolution (M.latentImpulse μ L t) σ := by
    funext k
    have hh:=M.discountedHistory_decomposition hμL t w
      (fun k=>gradient ψ (M.query w k)) hw k M.firstIndex
    rw [forcedState_convolution] at hh
    simpa only [discountedHistory,firstIndex,Nat.add_zero,f,σ,latentImpulse,Pi.add_apply] using hh
  rw [he]
  refine ⟨hf.1.add hc,(sequenceNorm_add_le hf.1 hc).trans ?_⟩
  change sequenceNorm f+sequenceNorm (convolution (M.latentImpulse μ L t) σ)≤_
  calc
    _≤M.latentFreeGain μ L t*M.stateNorm w 0+
        M.latentGainL2 μ L t*sequenceNorm σ:=add_le_add hfn hcn
    _≤M.latentFreeGain μ L t*M.stateNorm w 0+
        M.latentGainL2 μ L t*((M.feedbackConstant cert*M.queryFreeGain μ L t)*M.stateNorm w 0):=by
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left hs.2 (tsum_nonneg (fun n=>abs_nonneg (M.latentImpulse μ L t n)))
    _=M.executionGain cert*M.stateNorm w 0:=by unfold executionGain; ring

end Hilbert
end
end nesterov.StationaryMethod
