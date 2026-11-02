import krylov.Correction.CertificateArrays
import krylov.Methods.RFCPhase

/-!
Article: main_krylov, prop:deep, actual checked source-array execution.
Use: interpret the unchanged earlier integer checker expressions as true
physical source vectors, observed pair arrays, conjugacy and model solves,
line searches, genuine correction queries and returned RFC phase results.
Source: exact finite matrix certificate semantics and the existing original
RFC array executor, with the actual empty and accepted gate branches.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The genuine zero physical vector in the original certificate expression language.
Use: Represent the actual skipped empty-window correction exactly.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termZero (n : ℕ) : Fin n → Term := fun _ => .literal 0 1

/-- The compiled zero vector is exactly the genuine Euclidean zero.
Use: Preserve the real no-query correction branch.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Every interpreted coordinate is the exact rational zero. -/
theorem euclideanValue_zero (n : ℕ) (x : ℕ → ℝ) : euclideanValue (termZero n) x=0 := by
  ext i
  simp [euclideanValue,vectorValue,termZero,Expr.value]

/-- Appending the actual current query to a compiled stored family preserves its exact newest-first Euclidean interpretation.
Use: Keep the genuine augmented physical correction basis aligned with source storage.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: Split the true finite family into its head query and earlier recorded tail. -/
theorem euclideanValue_finCons {n p : ℕ} (d : Fin n → Term) (s : Fin p → Fin n → Term) (x : ℕ → ℝ) :
    (fun i : Fin (p+1) => euclideanValue ((Fin.cons d s : Fin (p+1) → Fin n → Term) i) x)=
      (Fin.cons (euclideanValue d x) (fun i : Fin p => euclideanValue (s i) x) : Fin (p+1) → EuclideanSpace ℝ (Fin n)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- The real one-correction RFC query expression, with the original empty-window skip.
Use: Compile the actual accepted correction branch without inventing an initial correction.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termPhaseQuery {n p : ℕ} (s y : Fin p → Fin n → Term) (g d z : Fin n → Term) : Fin n → Term :=
  if p=0 then termZero n else termModelQuery (Fin.cons d s)
    (termPairModel (Fin.cons d s) (Fin.cons z y)) (termPostSearch g d z)

/-- The genuine returned-gradient expression after the original real one-correction phase.
Use: Use the actual independent correction operator answer in the source certificate.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termPhaseGradient {n p : ℕ} (s y : Fin p → Fin n → Term) (g d z : Fin n → Term)
    (B : Matrix (Fin n) (Fin n) Term) : Fin n → Term :=
  termAdd (termPostSearch g d z) (termMatVec B (termPhaseQuery s y g d z))

/-- The actual total line-plus-correction evaluated-step expression.
Use: Keep true recorded total steps rather than line-only substitutes.
Article: main_krylov, prop:deep, actual checked RFC array execution. -/
def termPhaseStep {n p : ℕ} (s y : Fin p → Fin n → Term) (g d z : Fin n → Term) : Fin n → Term :=
  termAdd (termScale (termLineLength g d z) d) (termPhaseQuery s y g d z)

/-- The compiled phase returns exactly the genuine RFC array-phase gradient and recorded total step on each actually accepted nonempty gate and on the original empty-window skip.
Use: Connect checked arithmetic to the real original query executor before deriving any gate acceptance from the certificate.
Article: main_krylov, prop:deep, actual checked RFC array execution.
Proof: The empty branch makes the true zero query. On the accepted nonempty branch, genuine latest-model and physical synthesis semantics identify the actual correction tree; executing its one real query gives the returned gradient and movement exactly. -/
theorem termPhase_value {n p : ℕ} (s y : Fin p → Fin n → Term) (g d z : Fin n → Term)
    (B : Matrix (Fin n) (Fin n) Term) (x : ℕ → ℝ)
    (hgate : p=0 ∨ 0<p ∧ ‖pairDefect (fun i => euclideanValue (s i) x) (fun i => euclideanValue (y i) x)‖<1) :
    let phase := rfcArrayPhase (fun i => euclideanValue (s i) x) (fun i => euclideanValue (y i) x)
      (euclideanValue g x) (euclideanValue d x) (euclideanValue z x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixValue B x)) 1
    euclideanValue (termPhaseGradient s y g d z B) x=phase.gradient ∧
      euclideanValue (termPhaseStep s y g d z) x=
        Reference.lineLength (euclideanValue g x) (euclideanValue d x) (euclideanValue z x) • euclideanValue d x+phase.movement := by
  -- Preserve the true empty-window skip and execute exactly the real accepted one-query branch.
  dsimp only
  rcases hgate with hp | hp
  · subst p
    have hq : euclideanValue (termPhaseQuery s y g d z) x=0 := by
      rw [termPhaseQuery,ite_eq_left rfl]
      exact euclideanValue_zero n x
    simp only [termPhaseGradient,termPhaseStep,euclideanValue_add,euclideanValue_matVec,hq,
      euclideanValue_scale,termLineLength_value,termPostSearch_value,map_zero,add_zero,
      rfcArrayPhase,not_lt_zero,false_and,ite_false,and_self]
  · have hq : euclideanValue (termPhaseQuery s y g d z) x=
        combine (Fin.cons (euclideanValue d x) (fun i => euclideanValue (s i) x))
          (modelCoefficients (Fin.cons (euclideanValue d x) (fun i => euclideanValue (s i) x))
            (pairModel (Fin.cons (euclideanValue d x) (fun i => euclideanValue (s i) x))
              (Fin.cons (euclideanValue z x) (fun i => euclideanValue (y i) x)))
            (Reference.searchedGradient (euclideanValue g x) (euclideanValue d x) (euclideanValue z x))) := by
      rw [termPhaseQuery,ite_eq_right (Nat.ne_of_gt hp.1)]
      rw [termModelQuery_value,termPairModel_value,euclideanValue_finCons,euclideanValue_finCons,termPostSearch_value]
    simp only [termPhaseGradient,termPhaseStep,euclideanValue_add,euclideanValue_matVec,hq,
      euclideanValue_scale,termLineLength_value,termPostSearch_value,rfcArrayPhase,ite_eq_left hp,
      repeatedModelTree,runCorrections,add_zero,and_self]

end
end krylov.Correction.Certificate
