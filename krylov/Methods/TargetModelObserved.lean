import krylov.Methods.ModelObservedProgram

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, primitive target-relative model coefficients.
Use: compile actual latest-information corrections to a fixed prior gradient target using genuine finite observed coefficient rules.
Source: real linear observation synthesis and the proved smooth inverse-model solve on its genuine determinant domain.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- A genuine primitive observed rule synthesizes the actual inverse-model correction relative to a fixed prior target.
Use: A genuine primitive observed rule synthesizes the actual inverse-model correction relative to a fixed prior target.
Article: main_krylov, apB:prop:consist, primitive target-relative model coefficients.
Proof: Use the real synthesized basis and model with the true incoming gradient minus the prior target. -/
def targetModelObservedRule (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) (target : E) : ObservedRule E n where
  coefficient data := ∑ i,modelCoefficients (fun j => observationSynthesis data (s j)) (H data)
    (observationSynthesis data c-target) i • s i

/-- The actual target-relative observed rule evaluates exactly to the genuine physical inverse-model correction.
Use: The actual target-relative observed rule evaluates exactly to the genuine physical inverse-model correction.
Article: main_krylov, apB:prop:consist, primitive target-relative model coefficients.
Proof: Linear observation synthesis preserves the real finite coefficient sum. -/
theorem targetModelObservedRule_evaluate (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) (target : E) (data : Fin n → E) :
    (targetModelObservedRule s H c target).evaluate data=combine (fun j => observationSynthesis data (s j))
      (modelCoefficients (fun j => observationSynthesis data (s j)) (H data) (observationSynthesis data c-target)) := by
  change observationSynthesis data (∑ i,modelCoefficients (fun j => observationSynthesis data (s j))
    (H data) (observationSynthesis data c-target) i • s i)=_
  simp only [map_sum,map_smul,combine]

/-- Actual target-relative primitive model coefficients are C-r on the genuine nonsingular observed model domain.
Use: Actual target-relative primitive model coefficients are C-r on the genuine nonsingular observed model domain.
Article: main_krylov, apB:prop:consist, primitive target-relative model coefficients.
Proof: Apply the proved inverse-model coefficient calculus to genuine observed synthesis minus a fixed constant target. -/
theorem targetModelObservedRule_regular (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ)
    (c : Fin n → ℝ) (target : E) (data : Fin n → E) (r : WithTop ℕ∞)
    (hH : ∀ i j,ContDiffAt ℝ r (fun p => H p i j) data) (hdet : (H data).det≠0) :
    ContDiffAt ℝ r (targetModelObservedRule s H c target).coefficient data := by
  have hc := contDiff_modelCoefficients (fun p : Fin n → E => fun j => observationSynthesis p (s j)) H
    (fun p => observationSynthesis p c-target) data (fun j => (synthesis_contDiff (s j) r).contDiffAt)
    hH ((synthesis_contDiff c r).contDiffAt.sub contDiffAt_const) hdet
  change ContDiffAt ℝ r (fun p : Fin n → E => ∑ i,modelCoefficients
    (fun j => observationSynthesis p (s j)) (H p) (observationSynthesis p c-target) i • s i) data
  exact ContDiffAt.sum (fun i _ => (hc i).smul contDiffAt_const)
end
end krylov.Methods
