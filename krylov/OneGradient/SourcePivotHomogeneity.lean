import krylov.OneGradient.KnownBaseCubeExpansion
import krylov.Correction.TwoCorrections
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), genuine source coefficient homogeneity.
Use: exact actual physical attaining parameters give the original full
correlated coefficient times the true scale squared, including zero scale.
Source: original fresh-defect/staircase scaling and exact finite source
increment dictionaries; no output jet or maximizing parameter is assumed.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Information krylov.Correction krylov.Envelope
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original correlated known-reference coefficient in explicit
canonical prior, query increment and independent output matrices.
Use: source coefficient sharpness and actual physical families share
exactly the same genuine fresh defect and staircase expression.
Article: main_krylov, thm:local(b), original full reference pivot coefficient. -/
def informedReferencePivotCoefficient
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  let h := canonicalCGUnitStep base g n
  let f := freshDefect base g D (n+1)
  let q := inner ℝ h (cgOperator (R+∑ l∈range n,D l) h)
  staircaseOperator base g D F (n+1) f+q • cgOperator F h

/-- Exact actual source canonical parameters identify its genuine full
correlated coefficient with the original explicit reference expression.
Use: attaining physical families retain every actual prior/increment form.
Article: main_krylov, thm:local(b), actual source coefficient dictionary.
Proof: genuine finite old ranges select exactly the same increment
matrices in the source fresh defect, staircase and hidden diagonal; the
actual final canonical increment is the independent output form. -/
theorem informedSourcePivotCoefficient_of_parameters
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (S : Scenario (n+1)) (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hprior : relativeOperator base (S.base-base)=R)
    (hinc : ∀ l<n,canonicalIncrement base (oneGradientScenarioMatrices S n) l=D l)
    (hterm : canonicalIncrement base (oneGradientScenarioMatrices S n) n=F) :
    informedSourcePivotCoefficient base g S=informedReferencePivotCoefficient base g D R F := by
  let E := canonicalIncrement base (oneGradientScenarioMatrices S n)
  change (∀ l<n,E l=D l) at hinc
  change E n=F at hterm
  have hsum : (∑ l∈range n,E l)=∑ l∈range n,D l :=
    sum_congr rfl (fun l hl => hinc l (mem_range.mp hl))
  have hf : freshDefect base g E (n+1)=freshDefect base g D (n+1) := by
    unfold freshDefect
    simp only [Nat.add_sub_cancel]
    exact sum_congr rfl (fun l hl => by rw [hinc l (mem_range.mp hl)])
  have hL : staircaseOperator base g E (E n) (n+1)=staircaseOperator base g D F (n+1) := by
    unfold staircaseOperator
    simp only [Nat.add_sub_cancel,hterm]
    congr 1
    exact sum_congr rfl (fun l hl => by rw [hinc l (mem_range.mp hl)])
  change staircaseOperator base g E (E n) (n+1) (freshDefect base g E (n+1))+
    inner ℝ (canonicalCGUnitStep base g n) (cgOperator (relativeOperator base (S.base-base)+
      ∑ l∈range n,E l) (canonicalCGUnitStep base g n)) • cgOperator (E n) (canonicalCGUnitStep base g n)=_
  rw [hL,hf,hprior,hsum,hterm]
  rfl

/-- Scaling every genuine prior/query/output form scales the complete
original correlated source coefficient by exactly the square of the scale.
Use: native physical sharpness retains the real second-order coefficient,
including all zero scales and budgets, before any limiting argument.
Article: main_krylov, thm:local(b), exact source coefficient homogeneity.
Proof: reuse true fresh-defect and staircase scaling. The actual hidden
diagonal is linear in every matrix, so its real output product is quadratic. -/
theorem informedReferencePivotCoefficient_smul
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (t : ℝ) :
    informedReferencePivotCoefficient base g (fun l => t • D l) (t • R) (t • F)=
      t^2 • informedReferencePivotCoefficient base g D R F := by
  simp only [informedReferencePivotCoefficient,staircaseOperator_smul,freshDefect_smul,
    ← Finset.smul_sum,← smul_add,cgOperator,map_smul,_root_.smul_apply,map_smul,
    real_inner_smul_right,smul_smul]
  module

end
end krylov.OneGradient
