import krylov.Methods.ObservationSynthesis
import krylov.Methods.CorrectionProgram
import krylov.Methods.RepeatedCorrection
import krylov.Stability.ContDiffSolve

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Use: compile genuine repeated model corrections into primitive observed
coefficient queries, preserving the actual fixed model and basis and the
true newly returned gradient at every finite correction.
Source: actual finite linear observation synthesis and standard smooth
finite inverse-model coefficients on their true determinant domain.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The original true observed coefficients extended by zero on two newly available actual observations.
Use: The original true observed coefficients extended by zero on two newly available actual observations.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Prepend two genuine zero coefficients. -/
def liftCoefficientsTwo (c : Fin n → ℝ) : Fin (n+2) → ℝ := Fin.cons 0 (Fin.cons 0 c)

/-- Adding two actual observations leaves the synthesis of the original genuinely zero-extended coefficients unchanged.
Use: Adding two actual observations leaves the synthesis of the original genuinely zero-extended coefficients unchanged.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Expand the actual two finite sum heads, whose real coefficients are zero. -/
theorem observationSynthesis_lift_two (data : Fin n → E) (v w : E) (c : Fin n → ℝ) :
    observationSynthesis (Fin.cons v (Fin.cons w data) : Fin (n+2) → E) (liftCoefficientsTwo c)=
      observationSynthesis data c := by
  change combine (Fin.cons v (Fin.cons w data)) (Fin.cons 0 (Fin.cons 0 c))=combine data c
  simp only [combine,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,zero_smul,zero_add]

/-- The genuine primitive coefficient rule of an actual fixed-basis inverse-model correction.
Use: The genuine primitive coefficient rule of an actual fixed-basis inverse-model correction.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Compute true physical model coefficients from actually synthesized columns, the observed model and actual current gradient. -/
def modelObservedRule (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) : ObservedRule E n where
  coefficient data := ∑ i, modelCoefficients (fun j => observationSynthesis data (s j)) (H data)
    (observationSynthesis data c) i • s i

/-- The genuine primitive model rule evaluates exactly to the actual physical inverse-model correction.
Use: The genuine primitive model rule evaluates exactly to the actual physical inverse-model correction.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: The true linear synthesis map preserves the actual finite sum and real scalar products. -/
theorem modelObservedRule_evaluate (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) (data : Fin n → E) :
    (modelObservedRule s H c).evaluate data=combine (fun j => observationSynthesis data (s j))
      (modelCoefficients (fun j => observationSynthesis data (s j)) (H data) (observationSynthesis data c)) := by
  change observationSynthesis data (∑ i, modelCoefficients (fun j => observationSynthesis data (s j)) (H data)
    (observationSynthesis data c) i • s i)=_
  simp only [map_sum,map_smul,combine]

/-- Synthesis with genuine fixed coefficients is C-r in the actual finite observed data.
Use: Synthesis with genuine fixed coefficients is C-r in the actual finite observed data.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Sum the true finite constant multiples of actual coordinate projections. -/
theorem synthesis_contDiff (c : Fin n → ℝ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (fun data : Fin n → E => observationSynthesis data c) := by
  change ContDiff ℝ r (fun data : Fin n → E => ∑ i, c i • data i)
  exact ContDiff.sum fun i _ => contDiff_const.smul (contDiff_pi.mp contDiff_id i)

/-- The actual primitive model-correction coefficients are C-r on the true model determinant domain.
Use: The actual primitive model-correction coefficients are C-r on the true model determinant domain.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Compose proved true inverse-model coefficient regularity with genuine linear observed synthesis and sum the actual fixed coefficient vectors. -/
theorem modelObservedRule_regular (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) (data : Fin n → E) (r : WithTop ℕ∞)
    (hH : ∀ i j, ContDiffAt ℝ r (fun p => H p i j) data) (hdet : (H data).det≠0) :
    ContDiffAt ℝ r (modelObservedRule s H c).coefficient data := by
  have hc := contDiff_modelCoefficients (fun p : Fin n → E => fun j => observationSynthesis p (s j)) H
    (fun p => observationSynthesis p c) data (fun j => (synthesis_contDiff (s j) r).contDiffAt)
    hH (synthesis_contDiff c r).contDiffAt hdet
  change ContDiffAt ℝ r (fun p : Fin n → E => ∑ i, modelCoefficients
    (fun j => observationSynthesis p (s j)) (H p) (observationSynthesis p c) i • s i) data
  exact ContDiffAt.sum (fun i _ => (hc i).smul contDiffAt_const)

/-- A genuine finite primitive observed program for actual repeated fixed-model corrections.
Use: A genuine finite primitive observed program for actual repeated fixed-model corrections.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Every true continuation retains its original observed columns and model, and reads its actual newly returned gradient. -/
def repeatedObservedModel : (k : ℕ) → {n : ℕ} →
    (ι → Fin n → ℝ) → ((Fin n → E) → Matrix ι ι ℝ) → (Fin n → ℝ) → CorrectionProgram E n
  | 0, _, _, _, _ => .done
  | k+1, _, s, H, c => .query (modelObservedRule s H c)
      (repeatedObservedModel k (fun i => liftCoefficientsTwo (s i))
        (fun data => H (Fin.tail (Fin.tail data))) (Pi.single 0 1))

/-- The genuine compiled repeated primitive program is exactly the actual repeated physical model decision tree, for all true future oracle answers.
Use: The genuine compiled repeated primitive program is exactly the actual repeated physical model decision tree, for all true future oracle answers.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Induct over actual queries; zero extension preserves the true original model and basis, while the real new head observation is exactly the next incoming gradient. -/
theorem repeatedObservedModel_tree (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) (k : ℕ) (data : Fin n → E) :
    (repeatedObservedModel k s H c).tree data=
      repeatedModelTree (fun i => observationSynthesis data (s i)) (H data) k (observationSynthesis data c) := by
  -- Preserve the actual original columns and model while the genuine new gradient enters at the true head coordinate.
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change CorrectionTree.query ((modelObservedRule s H c).evaluate data) _=CorrectionTree.query _ _
    rw [modelObservedRule_evaluate]
    congr 1
    funext gnew
    rw [ih]
    simp only [observationSynthesis_lift_two,Fin.tail_cons]
    rw [observationSynthesis_single]
    rfl

/-- Every actual finite compiled model-correction query has C-r primitive coefficients on the true initial model domain.
Use: Every actual finite compiled model-correction query has C-r primitive coefficients on the true initial model domain.
Article: main_krylov, def:classes, cor:lm and thm:select, actual finite model-correction compilation.
Proof: Induct over genuine queries. The actual original model survives true zero extension, its determinant domain remains the same, and all real primitive coefficient maps are C-r. -/
theorem repeatedObservedModel_regular (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) (k : ℕ) (data : Fin n → E) (r : WithTop ℕ∞) (B : E →L[ℝ] E) (g : E)
    (hH : ∀ i j, ContDiffAt ℝ r (fun p => H p i j) data) (hdet : (H data).det≠0) :
    (repeatedObservedModel k s H c).RegularAt r B g data := by
  -- Each true query extends the actual observations; the real model determinant remains the original nonzero determinant.
  induction k generalizing n g with
  | zero => trivial
  | succ k ih =>
    refine ⟨modelObservedRule_regular s H c data r hH hdet,?_⟩
    let nextData : Fin (n+2) → E := Fin.cons (g+B ((modelObservedRule s H c).evaluate data))
      (Fin.cons ((modelObservedRule s H c).evaluate data) data)
    apply ih (fun i => liftCoefficientsTwo (s i)) (fun data : Fin (n+2) → E => H (Fin.tail (Fin.tail data))) (Pi.single 0 1) nextData
    · intro i j
      exact (hH i j).comp nextData (contDiffAt_pi.mpr fun l : Fin n => contDiffAt_pi.mp (show ContDiffAt ℝ r (fun p : Fin (n+2) → E => p) nextData from contDiffAt_id) l.succ.succ)
    · exact hdet
end
end krylov.Methods
