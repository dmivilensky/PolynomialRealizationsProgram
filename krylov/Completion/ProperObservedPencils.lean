import krylov.Methods.ProperKrylovPencils
import krylov.Completion.QuadraticObservedWindow
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau and s8:dcsdef, actual physical Schur domains.
Use: translate genuine proper-flag strict forms to the physical pencils
formed by the original observed columns and latest-information model.
Source: exact true quadratic window coordinates and proved strict Krylov Gram shifts.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace BigOperators
variable {n : ℕ}

/-- The physical Gram of actual observed columns is their genuine
Euclidean cross-Gram, in the same actual stored indexing.
Use: physical Schur-pencil and native coefficient coordinates agree exactly.
Article: main_krylov, thm:radau.
Proof: the genuine physical coordinate inner product is the finite dot product. -/
theorem observed_columns_gram
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :
    let S : Matrix (Fin n) (Fin W.length) ℝ := fun a j => windowSteps W j a
    Sᵀ*S=crossGram (windowSteps W) (windowSteps W) := by
  ext i j
  change (∑ a : Fin n,windowSteps W i a*windowSteps W j a)=
    inner ℝ (windowSteps W i) (windowSteps W j)
  rw [real_inner_comm]
  rfl

/-- Every genuine independent quadratic observed basis in a proper CG
flag has both original physical shifted Schur pencils positive definite.
Use: the native interval continuation's determinant domains are derived,
even at physical class spectral endpoints and collapsed information intervals.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: real quadratic observations identify the latest model with the actual
operator Gram. The physical observed Gram dictionary and strict proper-flag
Gram theorem give both actual positive pencils. -/
theorem proper_observed_window_pencils
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0)
    (mu upper : ℝ)
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator base v))
    (hhi : ∀ v : EuclideanSpace ℝ (Fin n),inner ℝ v (cgOperator base v)≤upper*‖v‖^2)
    (hy : ∀ j,windowImages W j=cgOperator base (windowSteps W j))
    (hLI : LinearIndependent ℝ (windowSteps W)) (hflag : ∀ j,windowSteps W j∈directionFlag (cgOperator base) g k) :
    let S : Matrix (Fin n) (Fin W.length) ℝ := fun a j => windowSteps W j a
    (windowModel W-mu • (Sᵀ*S)).PosDef ∧ (upper • (Sᵀ*S)-windowModel W).PosDef := by
  have hp := cgOperator_positive base hb
  have h := proper_directionFlag_gram_shifts (cgOperator base) hp.1 hp.2 g k hpre mu upper
    hlo hhi (windowSteps W) hLI hflag
  dsimp only
  rw [observed_columns_gram,windowModel_quadratic W (cgOperator base) hp.1 hy]
  exact h

end
end krylov.Completion
