import krylov.OneGradient.XRFCObservedSpectral
import krylov.Cancellation.DCSchurEstimate
import krylov.Stability.OneGradientTrialBridge
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, genuine smooth harmonic XRFC trial.
Use: continue the original observed harmonic rule through feasible boundary
and collapsed-interval references using only true recorded history data.
Source: the proved rational Schur endpoints, actual virtual-window calculus
and exact fixed-shape history reconstruction. -/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Cancellation krylov.Methods krylov.Reference krylov.Stability krylov.Completion
open scoped InnerProductSpace
variable {n m : ℕ}

/-- The actual full-window harmonic trial continued by ordinary Schur
inverses. Its direction is the genuine virtual XRFC direction.
Use: this data-only rule remains defined on neighboring infeasible histories.
Article: main_krylov, thm:radau and cor:quant(a). -/
def xrfcSchurHarmonic (mu upper : ℝ) (H : History (EuclideanSpace ℝ (Fin n))) : ℝ :=
  schurHarmonicTrial (xrfcPriorColumns H) (WithLp.ofLp (xrfcPriorDirection H))
    (windowModel H.pairs) mu upper
      (-inner ℝ (virtualGradient H.pairs H.gradient) (xrfcPriorDirection H))

/-- Positive totalization of the genuine observed Schur harmonic policy.
Use: actual full-memory XRFC always receives a nonzero trial on arbitrary data.
Article: main_krylov, thm:radau and cor:quant(a). -/
def xrfcSchurTrial (mu upper : ℝ) (H : History (EuclideanSpace ℝ (Fin n))) : ℝ :=
  if 0<xrfcSchurHarmonic mu upper H then xrfcSchurHarmonic mu upper H else 1

/-- The actual continued harmonic policy is positive on every history.
Use: real native basis and model domains follow from the executed policy.
Article: main_krylov, thm:radau.
Proof: the selected true value is positive or the policy returns one. -/
theorem xrfc_schur_trial_positive (mu upper : ℝ) (H : History (EuclideanSpace ℝ (Fin n))) :
    0<xrfcSchurTrial mu upper H := by
  unfold xrfcSchurTrial
  split_ifs with h
  · exact h
  · norm_num

/-- Length casting preserves the real harmonic Schur rule.
Use: fixed-shape history charts keep exactly the executed scalar value.
Article: main_krylov, thm:radau.
Proof: both true getter families and the actual latest model reindex together. -/
theorem schur_harmonic_window_coordinates
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (p : ℕ) (hp : W.length=p) (d : Fin n → ℝ) (mu upper q : ℝ) :
    schurHarmonicTrial (fun a j => windowSteps W j a) d (windowModel W) mu upper q=
      schurHarmonicTrial (fun a (j : Fin p) => (W.getD j.val (0,0)).1 a) d
        (pairModel (fun j : Fin p => (W.getD j.val (0,0)).1)
          (fun j : Fin p => (W.getD j.val (0,0)).2)) mu upper q := by
  subst p
  have hs : windowSteps W=(fun i : Fin W.length => (W.getD i.val (0,0)).1) :=
    windowSteps_getD_array W W.length rfl
  have hy : windowImages W=(fun i : Fin W.length => (W.getD i.val (0,0)).2) :=
    windowImages_getD_array W W.length rfl
  rw [← pairModel_window,hs,hy]

/-- The genuine virtual-direction Schur harmonic chart domain.
Use: the domain contains only the actual two model determinants, two shifted
pencils and positive real endpoint values; no regularity is assumed.
Article: main_krylov, thm:radau and lem:U(d). -/
def xrfcSchurChartDomain (shape : List ℕ)
    (data : Fin m → EuclideanSpace ℝ (Fin n)) (mu upper : ℝ) : Prop :=
  let s := chartSteps fullMemory shape data
  let y := chartImages fullMemory shape data
  let T := pairModel s y
  let S : Matrix (Fin n) (Fin (min (fullMemory shape.length) shape.length)) ℝ := fun a i => s i a
  let gv := chartGradient shape data+combine y (modelCoefficients s T (chartGradient shape data))
  let d := WithLp.ofLp (conjugacyDirection s y gv)
  T.det≠0 ∧ (crossGram y s).det≠0 ∧ (T-mu • (Sᵀ*S)).det≠0 ∧
    (upper • (Sᵀ*S)-T).det≠0 ∧ 0<schurLowerCurvature S d T mu ∧
      0<schurUpperCurvature S d T upper

/-- The true primitive full-history harmonic Schur continuation is C-r on
its actual algebraic domain.
Use: native trial regularity follows from observed entries and genuine solves.
Article: main_krylov, thm:radau and lem:U(d).
Proof: exact getter coordinates supply the actual virtual gradient and virtual
direction. The existing virtual-block calculus and literal Schur harmonic
calculus apply at their real determinants and positive endpoints. -/
theorem xrfc_schur_harmonic_chart_regular (shape : List ℕ)
    (data : Fin m → EuclideanSpace ℝ (Fin n)) (mu upper : ℝ) (r : WithTop ℕ∞)
    (hdomain : xrfcSchurChartDomain shape data mu upper) :
    ContDiffAt ℝ r (historyEstimateChart (xrfcSchurHarmonic mu upper) shape m) data := by
  let X := Fin m → EuclideanSpace ℝ (Fin n)
  let s := fun z : X => chartSteps fullMemory shape z
  let y := fun z : X => chartImages fullMemory shape z
  let G := fun z : X => chartGradient shape z
  let W := fun z : X => chartWindow fullMemory shape z
  let T := fun z : X => pairModel (s z) (y z)
  let S : X → Matrix (Fin n) (Fin (min (fullMemory shape.length) shape.length)) ℝ := fun z a i => s z i a
  let gv := fun z : X => G z+combine (y z) (modelCoefficients (s z) (T z) (G z))
  let D := fun z : X => conjugacyDirection (s z) (y z) (gv z)
  let d := fun z : X => WithLp.ofLp (D z)
  let q := fun z : X => -inner ℝ (gv z) (D z)
  obtain ⟨hm,hc,hl,hh,hlpos,hhpos⟩ := hdomain
  have hf := chartSteps_regular fullMemory shape (fun z : X => z) data (r := r) contDiffAt_id
  have hg := (chartWindow_regular fullMemory shape (fun z : X => z) data (r := r) contDiffAt_id).2
  have hb := contDiff_virtualBlock s y G data (fun i => (hf i).1) (fun i => (hf i).2) hg hm hc
  have hS (a : Fin n) (i : Fin (min (fullMemory shape.length) shape.length)) :
      ContDiffAt ℝ r (fun z => S z a i) data :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) a).contDiff.contDiffAt.comp data (hf i).1
  have hdcoord (a : Fin n) : ContDiffAt ℝ r (fun z => d z a) data :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) a).contDiff.contDiffAt.comp data hb.2.2
  have hT (i j : Fin (min (fullMemory shape.length) shape.length)) :
      ContDiffAt ℝ r (fun z => T z i j) data := (hf (max i j)).1.inner ℝ (hf (min i j)).2
  have hq : ContDiffAt ℝ r q data := (hb.2.1.inner ℝ hb.2.2).neg
  have h := (contDiff_schur_rules S d T q mu upper data hS hdcoord hT hq hl hh hlpos hhpos).2
  apply h.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro z
  let H := historyFromObservations shape (List.ofFn z)
  have hW : W z=H.pairs := selectedWindow_full H
  have hv := (virtualWindow_coordinates (W z) (chartWindow_length fullMemory shape z) (s z) (y z)
    (windowSteps_getD_array _ _ (chartWindow_length fullMemory shape z))
    (windowImages_getD_array _ _ (chartWindow_length fullMemory shape z)) (G z)).2
  have hD : xrfcPriorDirection H=D z := by
    unfold xrfcPriorDirection
    rw [← hW]
    change windowDirection (W z) (virtualGradient (W z) (G z))=_
    rw [hv,windowDirection_getD_array _ _ (chartWindow_length fullMemory shape z)]
    rfl
  change xrfcSchurHarmonic mu upper H=_
  unfold xrfcSchurHarmonic xrfcPriorColumns
  rw [hD,← hW]
  change schurHarmonicTrial (fun a j => windowSteps (W z) j a) (d z)
    (windowModel (W z)) mu upper (-inner ℝ (virtualGradient (W z) (G z)) (D z))=_
  rw [hv,schur_harmonic_window_coordinates (W z) _ (chartWindow_length fullMemory shape z)]
  rfl

end
end krylov.OneGradient
