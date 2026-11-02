import krylov.Cancellation.DCRadauEstimate
import krylov.Cancellation.DCObserved
import krylov.Completion.SchurTrialRegularity
import krylov.Stability.ContDiffWindows
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef, native smooth Schur estimate continuation.
Use: implement the original arithmetic interval rule by its literal rational
continuation and derive its genuine primitive observed-history smoothness.
Source: original retained-window data, exact finite getter coordinates and
the proved Schur/virtual/conjugacy calculus, with actual algebraic domains.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Completion
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n m : ℕ}

/-- The genuine observed Gauss--Radau arithmetic rule continued by its
ordinary-inverse Schur formulas to neighboring supplied histories.
Use: a native data-only estimate can be smooth outside physical feasibility.
Article: main_krylov, s8:dcsdef and lem:U(d). -/
def dcSchurGaussRadauEstimate (memory : ℕ → ℕ) (mu upper : ℝ) :
    History (EuclideanSpace ℝ (Fin n)) → ℝ := fun H =>
  schurArithmeticEstimate (dcObservedColumns memory H) (dcObservedUntilted memory H)
    (windowModel (selectedWindow memory H)) mu upper (dcCurvatureSlope memory H)

/-- The real native continuation agrees exactly with the original observed
arithmetic interval rule on every feasible positive-pencil history.
Use: only the off-feasibility continuation changes; no source reference
endpoint value or minimax choice is replaced.
Article: main_krylov, s8:dcsdef.
Proof: apply the proved original feasible-window Schur dictionary. -/
theorem dc_schur_estimate_original (memory : ℕ → ℕ) (mu upper : ℝ)
    (H : History (EuclideanSpace ℝ (Fin n))) (hmu : 0<mu) (hmuL : mu≤upper)
    (hS : Function.Injective (dcObservedColumns memory H).mulVec)
    (hd : dcObservedUntilted memory H∉LinearMap.range (dcObservedColumns memory H).mulVecLin)
    (hlo : (windowModel (selectedWindow memory H)-
      mu • ((dcObservedColumns memory H)ᵀ*dcObservedColumns memory H)).PosDef)
    (hhi : (upper • ((dcObservedColumns memory H)ᵀ*dcObservedColumns memory H)-
      windowModel (selectedWindow memory H)).PosDef)
    (hC : (windowCurvatureCompletions (dcObservedColumns memory H) (dcObservedUntilted memory H)
      (windowModel (selectedWindow memory H)) mu upper).Nonempty) :
    dcGaussRadauEstimate memory mu upper H=dcSchurGaussRadauEstimate memory mu upper H :=
  (observed_rules_schur_extension _ hS _ hd _ mu upper _ hmu hmuL hlo hhi hC).1

/-- Pure length casting preserves the genuine physical Schur rule in its
actual getter-array coordinates, including singular totalized data.
Use: differentiating a fixed history shape never changes the executed scalar.
Article: main_krylov, s8:dcsdef and lem:U(d).
Proof: after the true length equality, the existing exact getter coordinates
identify both original vector families and their actual latest model. -/
theorem schur_window_coordinates
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (p : ℕ) (hp : W.length=p) (d : Fin n → ℝ) (mu upper q : ℝ) :
    schurArithmeticEstimate (fun a j => windowSteps W j a) d (windowModel W) mu upper q=
      schurArithmeticEstimate (fun a (j : Fin p) => (W.getD j.val (0,0)).1 a) d
        (pairModel (fun j : Fin p => (W.getD j.val (0,0)).1)
          (fun j : Fin p => (W.getD j.val (0,0)).2)) mu upper q := by
  subst p
  have hs : windowSteps W=(fun j : Fin W.length => (W.getD j.val (0,0)).1) :=
    windowSteps_getD_array W W.length rfl
  have hy : windowImages W=(fun j : Fin W.length => (W.getD j.val (0,0)).2) :=
    windowImages_getD_array W W.length rfl
  rw [← pairModel_window,hs,hy]

/-- The finite actual algebraic domain for the native Schur estimate chart.
Use: only true model/pencil determinants and true endpoint values enter;
there is no smoothness or desired-response premise in the domain.
Article: main_krylov, s8:dcsdef and lem:U(d). -/
def dcSchurChartDomain (memory : ℕ → ℕ) (shape : List ℕ)
    (data : Fin m → EuclideanSpace ℝ (Fin n)) (mu upper : ℝ) : Prop :=
  let s := chartSteps memory shape data
  let y := chartImages memory shape data
  let T := pairModel s y
  let S : Matrix (Fin n) (Fin (min (memory shape.length) shape.length)) ℝ := fun a i => s i a
  let d := WithLp.ofLp (conjugacyDirection s y (chartGradient shape data))
  T.det≠0 ∧ (crossGram y s).det≠0 ∧ (T-mu • (Sᵀ*S)).det≠0 ∧
    (upper • (Sᵀ*S)-T).det≠0 ∧ 0<schurLowerCurvature S d T mu ∧
      0<schurUpperCurvature S d T upper

/-- The genuine native history-only Schur estimate has primitive C-r
observed coefficient regularity on its real algebraic chart domain.
Use: supplies the actual hypothesis of all original native DC Taylor and
compact estimates without assuming regularity of any trajectory or estimate.
Article: main_krylov, s8:dcsdef and lem:U(d).
Proof: genuine full-history reconstruction gives smooth actual retained
steps, images and current gradient. The true virtual and untilted conjugacy
solves give a smooth actual descent pairing; literal Schur calculus then
applies. Exact getter coordinates identify the original executed scalar. -/
theorem dc_schur_estimate_chart_regular (memory : ℕ → ℕ) (shape : List ℕ)
    (data : Fin m → EuclideanSpace ℝ (Fin n)) (mu upper : ℝ) (r : WithTop ℕ∞)
    (hdomain : dcSchurChartDomain memory shape data mu upper) :
    ContDiffAt ℝ r (historyEstimateChart (dcSchurGaussRadauEstimate memory mu upper) shape m) data := by
  let X := Fin m → EuclideanSpace ℝ (Fin n)
  let s := fun z : X => chartSteps memory shape z
  let y := fun z : X => chartImages memory shape z
  let G := fun z : X => chartGradient shape z
  let W := fun z : X => chartWindow memory shape z
  let T := fun z : X => pairModel (s z) (y z)
  let S : X → Matrix (Fin n) (Fin (min (memory shape.length) shape.length)) ℝ := fun z a i => s z i a
  let D := fun z : X => conjugacyDirection (s z) (y z) (G z)
  let d := fun z : X => WithLp.ofLp (D z)
  let gv := fun z : X => virtualGradient (W z) (G z)
  let q := fun z : X => -inner ℝ (gv z) (D z)
  obtain ⟨hm,hc,hl,hh,hlpos,hhpos⟩ := hdomain
  have hf := chartSteps_regular memory shape (fun z : X => z) data (r := r) contDiffAt_id
  have hg := (chartWindow_regular memory shape (fun z : X => z) data (r := r) contDiffAt_id).2
  have hb := contDiff_virtualBlock s y G data (fun i => (hf i).1) (fun i => (hf i).2) hg hm hc
  have hd := contDiff_conjugacyDirection s y G data (fun i => (hf i).1) (fun i => (hf i).2) hg hc
  have hgv : ContDiffAt ℝ r gv data := by
    apply hb.2.1.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro z
    exact (virtualWindow_coordinates (W z) (chartWindow_length memory shape z) (s z) (y z)
      (windowSteps_getD_array _ _ (chartWindow_length memory shape z))
      (windowImages_getD_array _ _ (chartWindow_length memory shape z)) (G z)).2
  have hS (a : Fin n) (i : Fin (min (memory shape.length) shape.length)) :
      ContDiffAt ℝ r (fun z => S z a i) data :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) a).contDiff.contDiffAt.comp data (hf i).1
  have hdcoord (a : Fin n) : ContDiffAt ℝ r (fun z => d z a) data :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) a).contDiff.contDiffAt.comp data hd
  have hT (i j : Fin (min (memory shape.length) shape.length)) :
      ContDiffAt ℝ r (fun z => T z i j) data := (hf (max i j)).1.inner ℝ (hf (min i j)).2
  have hq : ContDiffAt ℝ r q data := (hgv.inner ℝ hd).neg
  have h := (contDiff_schur_rules S d T q mu upper data hS hdcoord hT hq hl hh hlpos hhpos).1
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro z
  change schurArithmeticEstimate (fun a j => windowSteps (W z) j a)
    (fun a => windowDirection (W z) (G z) a) (windowModel (W z)) mu upper
    (-inner ℝ (gv z) (windowDirection (W z) (G z)))=_
  rw [schur_window_coordinates (W z) _ (chartWindow_length memory shape z)]
  have hD : windowDirection (W z) (G z)=D z :=
    windowDirection_getD_array _ _ (chartWindow_length memory shape z) _
  change schurArithmeticEstimate (S z) (fun a => windowDirection (W z) (G z) a) (T z)
    mu upper (-inner ℝ (gv z) (windowDirection (W z) (G z)))=_
  rw [hD]

end
end krylov.Cancellation
