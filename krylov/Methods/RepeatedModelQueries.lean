import krylov.Methods.CorrectionFollow
import krylov.Methods.NormalizedCorrection
import krylov.LinearAlgebra.CorrectionAsymptotics

/-!
Article: main_krylov, thm:C2(b), actual fixed-model corrections with distinct segment operators.
Use: each real correction observes its own actual operator action before
forming the next right-hand side; the constant-operator case is exactly the
existing repeated RFC decision-tree executor, including its complete trace.
Source: the genuine finite correction protocol and the exact projected
model-query identity. This is fixed-model iterative refinement (Moler67; Higham02).
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Execute actual fixed-model corrections, with an independently prescribed operator on every real correction segment.
Use: the next solve uses only the genuinely returned preceding gradient.
Article: main_krylov, thm:C2(b), independently varying last-correction operators. -/
def modelQueries (s : ι → E) (H : Matrix ι ι ℝ) (B : ℕ → E →L[ℝ] E) :
    ℕ → E → CorrectionResult E
  | 0, g => ⟨0,g,[]⟩
  | c+1, g =>
    let r := modelQueries s H B c g
    let u := combine s (modelCoefficients s H r.gradient)
    let gp := r.gradient+B c u
    ⟨r.movement+u,gp,r.trace++[(u,gp)]⟩

/-- Appending one true fixed-model query gives precisely the next existing RFC decision tree.
Use: connect chronological varying-operator execution to the original actual policy implementation.
Article: main_krylov, thm:C2(b), fixed-model query protocol.
Proof: induction retains each genuine first query and attaches the same
one-query continuation only after the old tree has actually terminated. -/
theorem repeatedModelTree_snoc (s : ι → E) (H : Matrix ι ι ℝ) (c : ℕ) (g : E) :
    repeatedModelTree s H (c+1) g=(repeatedModelTree s H c g).follow
      (fun v => .query (combine s (modelCoefficients s H v)) (fun _ => .done)) g := by
  induction c generalizing g with
  | zero => rfl
  | succ c ih =>
    simp only [repeatedModelTree,CorrectionTree.follow]
    congr 1
    exact funext ih

/-- With a common operator, chronological fixed-model queries are exactly the actual RFC tree execution in movement, gradient and complete observed trace.
Use: transfer the later ordered-product theorem to the genuine existing RFC executor.
Article: main_krylov, thm:C2(b), exact implementation dictionary.
Proof: append the real next query by the preceding tree identity and use
the already proved full execution law for followed correction protocols. -/
theorem modelQueries_constant (s : ι → E) (H : Matrix ι ι ℝ) (B : E →L[ℝ] E)
    (c : ℕ) (g : E) :
    (modelQueries s H (fun _ => B) c g).movement=(runCorrections (repeatedModelTree s H c g) B g).movement ∧
    (modelQueries s H (fun _ => B) c g).gradient=(runCorrections (repeatedModelTree s H c g) B g).gradient ∧
    (modelQueries s H (fun _ => B) c g).trace=(runCorrections (repeatedModelTree s H c g) B g).trace := by
  -- Preserve all real observations when replacing the chronological recursion by the actual tree.
  induction c with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ c ih =>
    obtain ⟨hm,hg,ht⟩ := ih
    rw [repeatedModelTree_snoc]
    have hf := CorrectionTree.run_follow (repeatedModelTree s H c g)
      (fun v => .query (combine s (modelCoefficients s H v)) (fun _ => .done)) B g
    dsimp only [modelQueries]
    rw [hm,hg,ht]
    simpa only [runCorrections,add_zero] using And.intro hf.1.symm ⟨hf.2.1.symm,hf.2.2.symm⟩

/-- Each chronological model correction spends exactly one real observed-gradient query.
Use: the varying-segment extension has the source's actual finite correction count.
Article: main_krylov, thm:C2(b), k_c correction queries.
Proof: the true trace appends one actual displacement/gradient pair per correction. -/
theorem modelQueries_count (s : ι → E) (H : Matrix ι ι ℝ) (B : ℕ → E →L[ℝ] E)
    (c : ℕ) (g : E) : (modelQueries s H B c g).trace.length=c := by
  induction c with
  | zero => rfl
  | succ c ih => simpa only [modelQueries,List.length_append,List.length_singleton] using congrArg Nat.succ ih

/-- A genuine model query applies the exact signed inverse-model error to its actual projected incoming gradient.
Use: every factor in the repeated product is derived from the actually queried operator.
Article: main_krylov, thm:C2(b), Uᵀg_p=−(UᵀB_pU−H)H⁻¹Uᵀg_(p−1).
Proof: lift the existing exact coefficient-query identity to its genuine Euclidean coefficient space. -/
theorem model_query_projected {p : ℕ} (s : Fin p → E) (H : Matrix (Fin p) (Fin p) ℝ)
    (hH : IsUnit H.det) (B : E →L[ℝ] E) (g : E) :
    projectedResidual s (g+B (combine s (modelCoefficients s H g)))=
      -(Matrix.toEuclideanCLM (𝕜 := ℝ) ((correctionCompression s B-H)*H⁻¹) (projectedResidual s g)) := by
  have he := modelCorrection_projected s H hH B g
  rw [Matrix.neg_mulVec] at he
  simpa only [projectedResidual,Matrix.toEuclideanCLM_toLp,WithLp.toLp_neg] using
    congrArg (WithLp.toLp 2) he

/-- The real varying-segment query executor has precisely the signed ordered residual recurrence.
Use: identify the genuine actual last-phase residual before invoking asymptotic product calculus.
Article: main_krylov, thm:C2(b), exact correction-product identity.
Proof: each genuine next gradient is the preceding observed gradient plus
the actual next operator action; the exact one-query projected identity
therefore advances the existing correction recurrence in the correct order. -/
theorem modelQueries_projected {α : Type*} {p : ℕ} (s : α → Fin p → E)
    (H : α → Matrix (Fin p) (Fin p) ℝ) (B : ℕ → α → E →L[ℝ] E)
    (g : α → E) (x : α) (hH : IsUnit (H x).det) (c : ℕ) :
    projectedResidual (s x) (modelQueries (s x) (H x) (fun j => B j x) c (g x)).gradient=
      correctionRun (fun j z => Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((correctionCompression (s z) (B j z)-H z)*(H z)⁻¹))
        (fun z => projectedResidual (s z) (g z)) c x := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change projectedResidual (s x) (_+B c x (combine (s x) (modelCoefficients (s x) (H x) _)))=_
    rw [model_query_projected (s x) (H x) hH,ih]
    rfl

end
end krylov.Methods
