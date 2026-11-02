import krylov.Correction.GatedExecution
import krylov.Correction.GatedCanonical
import krylov.Methods.CanonicalWindows
import krylov.Methods.FullProbedWindow
import krylov.Methods.DirectionStaircase

/-!
Article: main_krylov, thm:UCg, genuine observed-window execution dictionary.
Use: Connect uniform finite-array estimates to the actual dynamically sized
observed history, its real recorded pairs and original canonical fields.
Source: the existing genuine probed executor, true list-window model and gate
identities, exact original pair indexing and proved canonical phase covariance.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real spectral-gated correction executor equals its actual observed-list array phase through every genuine branch.
Use: Transfer the uniform cutoff induction directly to the genuine observed gated-RFC history.
Article: main_krylov, thm:UCg, actual observed-window execution.
Proof: Identify the actual augmented list model, true spectral test and original nonempty defect condition in the list own coefficient coordinates; execute both real tests.
-/
theorem gatedCorrection_window_phase (memory : ℕ → ℕ) (γ : ℝ) (H : History E) (z : E)
    (B : E →L[ℝ] E) :
    let W := selectedWindow memory H
    let d := windowDirection W H.gradient
    runCorrections (gatedCorrection memory γ H z) B (searchedGradient H.gradient d z)=
      gatedArrayPhase γ (windowSteps W) (windowImages W) H.gradient d z B := by
  classical
  let W := selectedWindow memory H
  let d := windowDirection W H.gradient
  have hmodel : windowModel ((d,z)::W)=pairModel (Fin.cons d (windowSteps W)) (Fin.cons z (windowImages W)) := by
    rw [← pairModel_window,windowSteps_cons,windowImages_cons]
  have hgate : spectralGate γ ((d,z)::W) ↔
      matrixSpectralGate γ (pairModel (Fin.cons d (windowSteps W)) (Fin.cons z (windowImages W))) := by
    rw [← matrixSpectralGate_window,hmodel]
  have hn : W≠[] ↔ 0<W.length := List.length_pos_iff_ne_nil.symm
  have hdef : windowDefect W=pairDefect (windowSteps W) (windowImages W) := rfl
  dsimp only
  unfold gatedCorrection
  dsimp only
  change runCorrections (if spectralGate γ ((d,z)::W) then rfcCorrection memory 1 H z else .done) B
    (searchedGradient H.gradient d z)=_
  rw [hgate]
  unfold gatedArrayPhase
  split
  · unfold rfcCorrection
    dsimp only
    change runCorrections (if W≠[] ∧ ‖windowDefect W‖<1 then
      repeatedModelTree (windowSteps ((d,z)::W)) (windowModel ((d,z)::W)) 1
        (searchedGradient H.gradient d z) else .done) B (searchedGradient H.gradient d z)=_
    simp only [hn,hdef,hmodel,windowSteps_cons]
    unfold rfcArrayPhase
    split <;> rfl
  · rfl

/-- The actual gated run returns exactly its genuine observed-list array phase at each real iteration.
Use: Transfer the uniform cutoff induction directly to the genuine observed gated-RFC history.
Article: main_krylov, thm:UCg, actual observed-window execution.
Proof: Specialize the original observed-window correction execution identity to the actual history and true current correction operator.
-/
theorem probedGated_phase_window (memory : ℕ → ℕ) (γ : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) :
    let m := gatedMethod memory γ (E := E)
    let H := methodRun m A B g i
    let W := selectedWindow memory H
    probedPhase m A B g i=gatedArrayPhase γ (windowSteps W) (windowImages W)
      H.gradient (m.direction H) (A i (m.direction H)) (B i) := by
  exact gatedCorrection_window_phase memory γ _ _ (B i)


/-- The actual next full retained history prepends exactly its real total step and measured consecutive-gradient secant.
Use: Transfer the uniform cutoff induction directly to the genuine observed gated-RFC history.
Article: main_krylov, thm:UCg, actual observed-window execution.
Proof: Use the genuine complete executed-pair transcript at the two actual consecutive indices.
-/
theorem full_observed_window_next (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) :
    selectedWindow fullMemory (methodRun m A B g (i+1))=
      (probedStep m A B g i,probedSecant m A B g i)::selectedWindow fullMemory (methodRun m A B g i) := by
  rw [fullWindow_methodRun,fullWindow_methodRun]
  rfl

/-- Every genuine retained observation inherits its true relative pair bound from the actual executed secant and total step, under any real memory rule.
Use: Transfer the uniform cutoff induction directly to the genuine observed gated-RFC history.
Article: main_krylov, thm:UCg, actual observed-window execution.
Proof: The original chronological indexing identifies each actual retained pair with a genuine earlier recorded iteration. Apply its proved real pair bound in the supplied true linear coordinates.
-/
theorem selectedWindow_pair_bound (memory : ℕ → ℕ) (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) (R J : E →L[ℝ] E) (η : ℝ)
    (herrors : ∀ j< i, ‖J (probedSecant m A B g j)-R (probedStep m A B g j)‖≤η*‖R (probedStep m A B g j)‖) :
    let W := selectedWindow memory (methodRun m A B g i)
    ∀ j : Fin W.length, ‖J (windowImages W j)-R (windowSteps W j)‖≤η*‖R (windowSteps W j)‖ := by
  let W := selectedWindow memory (methodRun m A B g i)
  have hw : W=(executedPairs (probedStep m A B g) (probedSecant m A B g) i).take (memory i) :=
    selectedWindow_methodRun memory m A B g i
  have hlen : W.length=min (memory i) i := by rw [hw,List.length_take,executedPairs_length]
  dsimp only
  intro j
  have hj : j.val< i := j.isLt.trans_le (hlen.le.trans (Nat.min_le_right (memory i) i))
  have he : W.get j=(probedStep m A B g (i-1-j.val),probedSecant m A B g (i-1-j.val)) := by
    change W[j.val]=_
    simp only [hw,List.getElem_take,executedPairs_get _ _ i j.val hj]
  have hs : windowSteps W j=probedStep m A B g (i-1-j.val) := congrArg Prod.fst he
  have hy : windowImages W j=probedSecant m A B g (i-1-j.val) := congrArg Prod.snd he
  change ‖J (windowImages W j)-R (windowSteps W j)‖≤η*‖R (windowSteps W j)‖
  rw [hy,hs]
  exact herrors _ (by omega)

/-- The actual observed gated phase, next returned gradient and full recorded step have their exact original primal/dual canonical fields.
Use: Transfer the uniform cutoff induction directly to the genuine observed gated-RFC history.
Article: main_krylov, thm:UCg, actual observed-window execution.
Proof: Use the actual observed-list phase dictionary and proved real canonical phase covariance. Genuine operator-action and exact-search covariance identify the actual line and full recorded displacement.
-/
theorem probedGated_canonical_window_fields {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (memory : ℕ → ℕ) (γ : ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    let m := gatedMethod memory γ (E := EuclideanSpace ℝ (Fin n))
    let H := methodRun m A B g i
    let W := selectedWindow memory H
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
    let d := R (m.direction H)
    let P := gatedArrayPhase γ (primalWindow base (windowSteps W)) (dualWindow base (windowImages W))
      (J H.gradient) d (canonicalOperator base (A i) d) (canonicalOperator base (B i))
    P.movement=R (probedPhase m A B g i).movement ∧
      P.gradient=J (probedGradient m A B g (i+1)) ∧
      lineLength (J H.gradient) d (canonicalOperator base (A i) d) • d+P.movement=
        R (probedStep m A B g i) := by
  let m := gatedMethod memory γ (E := EuclideanSpace ℝ (Fin n))
  let H := methodRun m A B g i
  let W := selectedWindow memory H
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
  have hc := gatedArrayPhase_canonical base hb γ (windowSteps W) (windowImages W)
    H.gradient (m.direction H) (A i (m.direction H)) (B i)
  rw [← probedGated_phase_window] at hc
  dsimp only
  rw [canonicalOperator_primal base hb]
  refine ⟨hc.1,hc.2,?_⟩
  rw [hc.1,canonical_lineLength base hb]
  rw [probedStep,map_add,map_smul]

/-- Every actual observed column in a nonsingular old solve has a genuinely nonzero canonical step.
Use: Derive the real normalization and conjugacy domains for the actual uniform cutoff induction.
Article: main_krylov, thm:UCg, true observed-window domains.
Proof: The true old coefficient determinant forces the physical column nonzero. The real inverse metric root cancels any proposed zero canonical image.
-/
theorem canonical_window_steps_ne_zero {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hC : IsUnit (crossGram (windowImages W) (windowSteps W)).det) (i : Fin W.length) :
    primalWindow base (windowSteps W) i≠0 := by
  intro hz
  have ht := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹) hz
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base) (windowSteps W i))=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹ 0 at ht
  rw [canonical_primal_dual_cancel base hb,map_zero] at ht
  exact crossGram_right_ne_zero (windowSteps W) (windowImages W) hC i ht

/-- The real nonsingular observed direction solve annihilates every genuine canonical old image.
Use: Derive the real normalization and conjugacy domains for the actual uniform cutoff induction.
Article: main_krylov, thm:UCg, true observed-window domains.
Proof: Apply the actual conjugacy coefficient equation and the true primal/dual root pairing to the original observed data.
-/
theorem canonical_window_image_conjugacy {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n))
    (hC : IsUnit (crossGram (windowImages W) (windowSteps W)).det) (i : Fin W.length) :
    inner ℝ (dualWindow base (windowImages W) i)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base) (windowDirection W g))=0 := by
  have hc := congrFun (conjugacyDirection_conjugate (windowSteps W) (windowImages W) g hC) i
  dsimp only [dualWindow]
  rw [real_inner_comm,← canonical_search_pairing base hb,real_inner_comm]
  exact hc

end
end krylov.Correction
