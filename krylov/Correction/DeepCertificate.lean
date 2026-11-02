import krylov.Correction.DeepExpressions
import krylov.Correction.CertificateContinuity

/-!
Article: main_krylov, prop:deep, checked source arithmetic and real continuity.
Use: Reuse the unchanged earlier-package integer checker to derive actual
source-expression enclosures and continuity from completely checked data.
Source: IntegerExpression.source_enclosed and original checker soundness;
continuity of real field operations on their certified reciprocal domains.
-/

namespace krylov.Correction.Certificate
noncomputable section
open chebyshev2.Numerics.IntegerCertificate

/-- The rational field-operation predicate is decidable by the original finite instruction constructors.
Use: Kernel-check that the original numerical graph uses only real field operations.
Article: main_krylov, prop:deep, exact original numerical certificate. -/
instance rationalOpDecidable (op : Op) : Decidable (rationalOp op) := by
  cases op <;> simp only [rationalOp] <;> infer_instance

/-- The common exact power-of-two scale of the original integer interval certificate.
Use: Retain sufficient exact precision for the printed very small determinant signs.
Article: main_krylov, prop:deep, exact original numerical certificate. -/
def deepScale : ℕ := 2^1152

/-- The original exact certificate scale is strictly positive.
Use: Apply the reused real enclosure and continuity soundness theorems.
Article: main_krylov, prop:deep, exact original numerical certificate.
Proof: A positive natural base has a positive natural power. -/
theorem deepScale_pos : 0<deepScale := by decide +kernel

/-- A finite original-source arithmetic program with every output independently decoded and all operations proved rational.
Use: Share the same genuine RFC source identities across all exact numerical domains.
Article: main_krylov, prop:deep, exact original numerical certificate.
-/
structure SourceProgram (k : Fin 4) where
  /-- The original exact rational arithmetic instruction list. -/
  operations : List Op
  /-- The final original stack index of each independently specified output. -/
  indices : Fin (sourceOutputs k).length → ℕ
  /-- Every original instruction uses only rational real field operations. -/
  rational : ∀ op∈operations, rationalOp op
  /-- Every checked stack expression is exactly its independently specified actual source expression. -/
  decodes : ∀ i, codeExpressionCheck operations (indices i) ((sourceOutputs k).get i)=true

/-- A completely accepted integer enclosure of an independently decoded actual source program.
Use: Discharge all real source output bounds through the existing sound checker.
Article: main_krylov, prop:deep, exact original numerical certificate.
-/
structure SourceEnclosure {k : Fin 4} (p : SourceProgram k) (scale : ℕ) where
  /-- The complete exact original input interval stack. -/
  inputs : List Bounds
  /-- The proposed exact integer enclosure of each original arithmetic operation. -/
  bounds : List Bounds
  /-- The exact final certified interval for every original source output. -/
  outputs : Fin (sourceOutputs k).length → Bounds
  /-- The enclosure annotation has exactly one interval per original instruction. -/
  length_eq : bounds.length=p.operations.length
  /-- The unchanged earlier-package integer checker accepts every arithmetic and reciprocal-domain annotation. -/
  accepted : programCheck scale inputs (annotate p.operations bounds)=true
  /-- Each original output index selects precisely its claimed checked final interval. -/
  lookup : ∀ i, (programBounds inputs (annotate p.operations bounds))[p.indices i]?=some (outputs i)

/-- Every completely checked source output lies in its exact certified real interval.
Use: Turn literal accepted integer data into genuine original RFC inequalities.
Article: main_krylov, prop:deep, exact original numerical certificate.
Proof: Use the unchanged checker soundness and independently decoded original expression.
-/
theorem SourceEnclosure.enclosed {k : Fin 4} {p : SourceProgram k} {scale : ℕ}
    (c : SourceEnclosure p scale) (hs : 0<scale) {x : ℕ → ℝ}
    (hx : Encloses scale c.inputs x) (i : Fin (sourceOutputs k).length) :
    (c.outputs i).Mem scale (((sourceOutputs k).get i).value x) := by
  exact source_enclosed hs _ hx c.accepted
    (expressionCheck_of_code c.length_eq (p.decodes i)) (c.lookup i)

/-- Every checked original source output is continuous on its actual enclosed input family.
Use: Derive the real determinant continuity needed by the original singular-family argument.
Article: main_krylov, prop:deep, exact original numerical certificate.
Proof: Use the unchanged checker soundness and independently decoded original expression.
-/
theorem SourceEnclosure.continuousOn {X : Type*} [TopologicalSpace X]
    {k : Fin 4} {p : SourceProgram k} {scale : ℕ}
    (c : SourceEnclosure p scale) (hs : 0<scale) {x : X → ℕ → ℝ} {K : Set X}
    (hx : ∀ t∈K, Encloses scale c.inputs (x t))
    (hc : ∀ j, ContinuousOn (fun t => x t j) K) (i : Fin (sourceOutputs k).length) :
    ContinuousOn (fun t => ((sourceOutputs k).get i).value (x t)) K := by
  -- Checker acceptance supplies actual nonzero reciprocal domains; decode the same final stack expression.
  have hrat : ∀ z∈annotate p.operations c.bounds, rationalOp z.op := by
    intro z hz
    apply p.rational z.op
    rw [← annotate_ops p.operations c.bounds c.length_eq]
    exact List.mem_map_of_mem hz
  have hp := checked_program_continuousOn hs (annotate p.operations c.bounds) hrat hx hc c.accepted (p.indices i)
  have he := expressionCheck_of_code c.length_eq (p.decodes i)
  have hsource : programExpression Expr.input (annotate p.operations c.bounds) (p.indices i)=(sourceOutputs k).get i := of_decide_eq_true he
  have hval : ∀ t, ((sourceOutputs k).get i).value (x t)=programValue (x t) (annotate p.operations c.bounds) (p.indices i) := by
    intro t
    rw [← hsource,programExpression_value]
    rfl
  simpa only [hval] using hp

end
end krylov.Correction.Certificate
