import krylov.Convergence.ObservableLine
import krylov.Convergence.ObservableProbeAngles
import krylov.Convergence.ObservableModelEnergy
import krylov.Convergence.ObservableCurvature

/-!
Article: main_krylov, apG:Dunif, genuine proposed RFC model.
Use: prepare the actual proposed correction and observed energies from
the true scalar source and the proved running-state invariant, before
deciding whether the observable energy test stops the cycle.
Source: actual metric search, measured conjugacy, derived augmented
conditioning and exact physical/model-energy coordinate dictionaries.
The segment Hessian below belongs to the proof, never to the algorithm.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
  krylov.Correction krylov.XR chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- True canonical Hessian average of the actually queried line segment.
Article: main_krylov, apG:Dunif. -/
def observableRFCSearchOperator (T : E ≃L[ℝ] E) (f : E → ℝ)
    (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (B : History E) : E →L[ℝ] E :=
  averagedDerivative (coordinateDerivative T H) (T (x₀+B.displacement))
    (T (rfcFunctionLinePoint T f fullMemory r x₀ B)-T (x₀+B.displacement))

/-- The actual canonical new direction followed by all real stored steps.
Article: main_krylov, apG:Dunif. -/
def observableRFCModelSteps (T : E ≃L[ℝ] E) (B : History E) : Fin (B.pairs.length+1) → E :=
  Fin.cons (T (rfcFunctionDirection fullMemory B)) (observablePrimal T B)

/-- The true averaged probe image followed by the actually observed dual
secants. Its new image is identified with the real finite difference.
Article: main_krylov, apG:Dunif. -/
def observableRFCModelImages (T : E ≃L[ℝ] E) (f : E → ℝ)
    (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (B : History E) : Fin (B.pairs.length+1) → E :=
  Fin.cons (observableRFCSearchOperator T f H r x₀ B (T (rfcFunctionDirection fullMemory B)))
    (observableDual T B)

/-- The actual line-endpoint gradient in its genuine dual coordinates.
Article: main_krylov, apG:Dunif. -/
def observableRFCLineGradient (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (B : History E) : E := T.symm (G (rfcFunctionLinePoint T f fullMemory r x₀ B))

/-- The proof's exact canonical direction-frame model coefficients; the
physical observed solve is proved to give precisely these coefficients
after its one-axis line rescaling. Article: main_krylov, apG:Dunif. -/
def observableRFCModelWeights (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (B : History E) : Fin (B.pairs.length+1) → ℝ :=
  modelCoefficients (observableRFCModelSteps T B)
    (pairModel (observableRFCModelSteps T B) (observableRFCModelImages T f H r x₀ B))
    (observableRFCLineGradient T f G r x₀ B)

/-- The actual proposed correction in the proved direction coordinates.
Article: main_krylov, apG:Dunif. -/
def observableRFCModelMove (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (B : History E) : E :=
  combine (observableRFCModelSteps T B) (observableRFCModelWeights T f G H r x₀ B)

/-- The true quadratic energy of that same observed coefficient solve.
Article: main_krylov, apG:Dunif. -/
def observableRFCModelEnergy (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (B : History E) : ℝ :=
  let w := observableRFCModelWeights T f G H r x₀ B
  w ⬝ᵥ (pairModel (observableRFCModelSteps T B) (observableRFCModelImages T f H r x₀ B)*ᵥw)

/-- All prepared model assertions are conclusions from the original
function and actual running invariant; this structure is not a source
hypothesis. Article: main_krylov, apG:Dunif. -/
structure ObservableRFCPrepared (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (B : History E) (epsilon : ℝ) : Prop where
  point : ‖T (rfcFunctionLinePoint T f fullMemory r x₀ B)‖≤2*‖T x₀‖
  value : f (rfcFunctionLinePoint T f fullMemory r x₀ B)≤f (x₀+B.displacement)
  direction : T (rfcFunctionDirection fullMemory B)≠0
  operator : ‖observableRFCSearchOperator T f H r x₀ B-ContinuousLinearMap.id ℝ E‖≤epsilon
  symmetry : (observableRFCSearchOperator T f H r x₀ B).toLinearMap.IsSymmetric
  alpha : 0<lineLength (T.symm B.gradient) (T (rfcFunctionDirection fullMemory B))
    (observableRFCSearchOperator T f H r x₀ B (T (rfcFunctionDirection fullMemory B)))
  line : T (rfcFunctionLineStep T f fullMemory r x₀ B)=
    lineLength (T.symm B.gradient) (T (rfcFunctionDirection fullMemory B))
      (observableRFCSearchOperator T f H r x₀ B (T (rfcFunctionDirection fullMemory B))) •
        T (rfcFunctionDirection fullMemory B)
  searched : observableRFCLineGradient T f G r x₀ B=
    searchedGradient (T.symm B.gradient) (T (rfcFunctionDirection fullMemory B))
      (observableRFCSearchOperator T f H r x₀ B (T (rfcFunctionDirection fullMemory B)))
  step : T (rfcFunctionLineStep T f fullMemory r x₀ B)≠0
  length : ‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖≤4*‖T x₀‖
  gram : ‖crossGram (unitWindow (observableRFCModelSteps T B))
    (unitWindow (observableRFCModelSteps T B))-1‖≤1/4
  correction : T (rfcFunctionCorrectionStep T f G fullMemory r x₀ B)=observableRFCModelMove T f G H r x₀ B
  energy : observableCorrectionEnergy T f G r x₀ B=observableRFCModelEnergy T f G H r x₀ B
  energy_nonneg : 0≤observableRFCModelEnergy T f G H r x₀ B
  move_energy : ‖observableRFCModelMove T f G H r x₀ B‖^2≤(5/3:ℝ)*observableRFCModelEnergy T f G H r x₀ B
  energy_move : observableRFCModelEnergy T f G H r x₀ B≤(5/3:ℝ)*‖observableRFCModelMove T f G H r x₀ B‖^2
  slope : inner ℝ (observableRFCLineGradient T f G r x₀ B) (observableRFCModelMove T f G H r x₀ B)=
    -observableRFCModelEnergy T f G H r x₀ B

/-- Actual source data and the true running invariant derive the entire
proposed observed model before deciding its energy gate, including the
original empty-memory branch. Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.prepare_rfc {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (B : History E) (N : ℕ) (epsilon bar : ℝ)
    (I : ObservableRFCInvariant T f G x₀ N epsilon bar B)
    (hn : 1≤N) (hsize : B.records.length<N) (he : 0≤epsilon) (hb : 0≤bar)
    (hsmall : (N:ℝ)*epsilon≤1/128) (hbar : (N:ℝ)*bar≤1/16)
    (hstart : ‖T x₀‖<r/4) (hsource : 2*(L:ℝ)*‖T x₀‖≤epsilon)
    (hslope : inner ℝ B.gradient (rfcFunctionDirection fullMemory B)<0) :
    ObservableRFCPrepared T f G H r x₀ B epsilon := by
  let d := T (rfcFunctionDirection fullMemory B)
  let A := observableRFCSearchOperator T f H r x₀ B
  let alpha := lineLength (T.symm B.gradient) d (A d)
  have hline := S.line_localization x₀ B hstart I.point I.value
  obtain ⟨hstep,hsearched,hsym,hA,halpha,hstep0⟩ := S.line_model_data x₀ B hstart I.point I.value I.gradient hslope
  have hlin : T (rfcFunctionLineStep T f fullMemory r x₀ B)=alpha • d := by
    rw [rfcFunctionLineStep,map_sub]
    exact hstep
  have hgline : observableRFCLineGradient T f G r x₀ B=searchedGradient (T.symm B.gradient) d (A d) := by
    simpa only [observableRFCLineGradient,coordinateGradient,T.symm_apply_apply,
      d,A,observableRFCSearchOperator] using hsearched
  have hsecant : T.symm (G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient)=alpha • A d := by
    rw [map_sub]
    change observableRFCLineGradient T f G r x₀ B-T.symm B.gradient=_
    rw [hgline,searchedGradient,add_sub_cancel_left]
  have hd : d≠0 := by
    intro hz
    have hzline := hlin
    rw [hz,smul_zero] at hzline
    apply hstep0
    simpa only [rfcFunctionLineStep,map_sub] using hzline
  have hlength : ‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖≤4*‖T x₀‖ := by
    rw [rfcFunctionLineStep,map_sub]
    exact (norm_sub_le _ _).trans (by linarith only [hline.1,I.point])
  have hdomains := I.domains S.inverse_symmetric hn hsize.le he hb hsmall hbar
  have ho (i : Fin B.pairs.length) : inner ℝ (observableDual T B i) d=0 :=
    observable_direction_conjugate T S.inverse_symmetric B hdomains.1 i
  have hU (i : Fin (B.pairs.length+1)) : observableRFCModelSteps T B i≠0 :=
    Fin.cases hd I.steps i
  have hUA : ‖A-ContinuousLinearMap.id ℝ E‖≤epsilon := hA.trans hsource
  have hY (i : Fin (B.pairs.length+1)) :
      ‖observableRFCModelImages T f H r x₀ B i-observableRFCModelSteps T B i‖≤
        (2*epsilon)*‖observableRFCModelSteps T B i‖ := by
    refine Fin.cases ?_ (fun j=>I.pairs j) i
    have hh := ((A-ContinuousLinearMap.id ℝ E).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right hUA (norm_nonneg d))
    simp only [_root_.sub_apply,ContinuousLinearMap.id_apply] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : epsilon≤2*epsilon) (norm_nonneg d))
  have hang := observable_probe_angles (observablePrimal T B) (observableDual T B) d I.steps hd
    (2*epsilon) (2*epsilon+3*bar) (by linarith) I.pairs ho I.angles
  have hdim : B.pairs.length+1≤N := by rw [History.pairs_length];omega
  have hUdomains := observable_rfc_window_domains (observableRFCModelSteps T B)
    (observableRFCModelImages T f H r x₀ B) hU N epsilon bar hn hdim he hb hsmall hbar hY hang
  have henergy := observable_raw_model_energy (observableRFCModelSteps T B)
    (observableRFCModelImages T f H r x₀ B) hU (observableRFCLineGradient T f G r x₀ B)
    hUdomains.1 hUdomains.2.1 hUdomains.2.2.2.1
  have hcorr : T (rfcFunctionCorrectionStep T f G fullMemory r x₀ B)=observableRFCModelMove T f G H r x₀ B := by
    by_cases hW : B.pairs=[]
    · have hw : selectedWindow fullMemory B=[] := by simpa only [selectedWindow_full] using hW
      have hreal := (observableRFC_empty T f G r x₀ B hw).1
      have horth : inner ℝ d (observableRFCLineGradient T f G r x₀ B)=0 := by
        rw [real_inner_comm]
        simpa only [observableRFCLineGradient,coordinateGradient,T.symm_apply_apply,d] using hline.2.2
      have hzero := (observableRFCMetric_empty T B.pairs d (A d) (observableRFCLineGradient T f G r x₀ B) hW horth).1
      rw [hreal,map_zero]
      convert hzero.symm using 1
      rfl
    · have hg : rfcFunctionGate fullMemory B := ⟨by simpa only [selectedWindow_full] using hW,hdomains.2.1⟩
      have hh := rfcFunctionCorrectionStep_metric T S.inverse_symmetric f G r x₀ B d (A d) halpha.ne' hlin hsecant hg
      dsimp only [observableRFCMetricSteps,observableRFCMetricImages] at hh
      rw [selectedWindow_full] at hh
      convert hh using 1
      rfl
  have hE : observableCorrectionEnergy T f G r x₀ B=observableRFCModelEnergy T f G H r x₀ B := by
    by_cases hW : B.pairs=[]
    · have hw : selectedWindow fullMemory B=[] := by simpa only [selectedWindow_full] using hW
      have hreal := (observableRFC_empty T f G r x₀ B hw).2
      have horth : inner ℝ d (observableRFCLineGradient T f G r x₀ B)=0 := by
        rw [real_inner_comm]
        simpa only [observableRFCLineGradient,coordinateGradient,T.symm_apply_apply,d] using hline.2.2
      have hzero := (observableRFCMetric_empty T B.pairs d (A d) (observableRFCLineGradient T f G r x₀ B) hW horth).2
      rw [hreal]
      convert hzero.symm using 1
      rfl
    · have hg : rfcFunctionGate fullMemory B := ⟨by simpa only [selectedWindow_full] using hW,hdomains.2.1⟩
      have hh := observableCorrectionEnergy_metric T S.inverse_symmetric f G r x₀ B d (A d) halpha.ne' hlin hsecant hg
      dsimp only [observableRFCMetricSteps,observableRFCMetricImages] at hh
      rw [selectedWindow_full] at hh
      convert hh using 1
      rfl
  exact ⟨hline.1,hline.2.1,hd,hUA,hsym,halpha,hlin,hgline,by
    rw [rfcFunctionLineStep,map_sub];exact hstep0,hlength,hUdomains.1,hcorr,hE,
    henergy.1,henergy.2.1,henergy.2.2.1,henergy.2.2.2⟩

end
end krylov.Convergence
