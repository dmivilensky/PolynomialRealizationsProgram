import chebyshev2.Numerics.IntegerExpression
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, prop:deep, genuine source execution and singular-model certification.
Use: Real continuity derived from the unchanged earlier integer checker and its actual reciprocal domains.
Source: original RFC array execution, earlier-package integer checker
soundness, standard real continuity and the intermediate value theorem.
-/

namespace krylov.Correction.Certificate
noncomputable section
open chebyshev2.Numerics.IntegerCertificate
variable {X : Type*} [TopologicalSpace X]

/-- The arithmetic operations of the unchanged earlier checker language that use only rational field arithmetic.
Use: Separate the genuine determinant certificate from the earlier optional positive cubic-root operation.
Article: main_krylov, prop:deep, actual checked source-family argument. -/
def rationalOp : Op → Prop
  | .cubic _ _ => False
  | _ => True

/-- Every accepted rational checker operation preserves genuine real continuity on its certified input domain.
Use: Derive real determinant continuity from the same checked arithmetic that supplies its numerical bounds.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: Addition, negation and multiplication preserve continuity. For a reciprocal, original checker acceptance proves its input interval has a strictly positive lower endpoint; actual enclosure then proves its genuine denominator is nonzero throughout the domain. -/
theorem checked_op_continuousOn (op : Op) (hrat : rationalOp op)
    {scale : ℕ} (hs : 0<scale) {stack : List Bounds} {R : Bounds}
    {v : X → ℕ → ℝ} {K : Set X}
    (hv : ∀ x∈K, Encloses scale stack (v x))
    (hcont : ∀ i, ContinuousOn (fun x => v x i) K)
    (hcheck : op.check scale stack R=true) :
    ContinuousOn (fun x => op.value (v x)) K := by
  -- Use original checker positivity to exclude every real reciprocal denominator zero.
  cases op with
  | literal a b => exact continuousOn_const
  | copy a => exact hcont a
  | add a b => exact (hcont a).add (hcont b)
  | neg a => exact (hcont a).neg
  | mul a b => exact (hcont a).mul (hcont b)
  | cubic a b => exact hrat.elim
  | inv a =>
    cases ha : stack[a]? with
    | none => simp only [Op.check,ha,Option.map_none,Option.getD_none,Bool.false_eq_true] at hcheck
    | some A =>
      have hc : invCheck scale A R=true := by simpa only [Op.check,ha,Option.map_some,Option.getD_some] using hcheck
      have hA : (0 : ℤ)<A.lo := (of_decide_eq_true hc).1
      have hAr : (0 : ℝ)<(A.lo : ℝ) := by exact_mod_cast hA
      have hscale : (0 : ℝ)<scale := by exact_mod_cast hs
      exact (hcont a).inv₀ (by
        intro x hx
        have he := (hv x hx a A ha).1
        have hn : 0<v x a := by nlinarith
        exact hn.ne')

/-- A completely accepted rational arithmetic program has genuinely continuous real output values throughout its certified input domain.
Use: Use the actual validated determinant program in the source intermediate-value argument.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: Induct over the original checked operation list. The existing checker soundness theorem supplies the actual next enclosure, and the genuine one-operation continuity theorem supplies its real continuous value. Both invariants pass through the same original stack update. -/
theorem checked_program_continuousOn {scale : ℕ} (hs : 0<scale) (nodes : List Node)
    (hrat : ∀ node∈nodes, rationalOp node.op)
    {stack : List Bounds} {v : X → ℕ → ℝ} {K : Set X}
    (hv : ∀ x∈K, Encloses scale stack (v x))
    (hcont : ∀ i, ContinuousOn (fun x => v x i) K)
    (hcheck : programCheck scale stack nodes=true) :
    ∀ i, ContinuousOn (fun x => programValue (v x) nodes i) K := by
  -- Propagate genuine real continuity and actual interval enclosure through the same checked stack.
  induction nodes generalizing stack v with
  | nil => exact hcont
  | cons node nodes ih =>
    have hc : node.op.check scale stack node.result=true ∧
        programCheck scale (node.result::stack) nodes=true := by
      simpa only [programCheck,Bool.and_eq_true] using hcheck
    have hop := checked_op_continuousOn node.op (hrat node (List.mem_cons_self)) hs hv hcont hc.1
    let w := fun x i => match i with
      | 0 => node.op.value (v x)
      | j+1 => v x j
    have hw : ∀ x∈K, Encloses scale (node.result::stack) (w x) := by
      intro x hx i I hi
      cases i with
      | zero =>
        have he : node.result=I := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using hi
        subst I
        exact node.op.check_sound hs (hv x hx) hc.1
      | succ j =>
        exact hv x hx j I (by simpa only [List.getElem?_cons_succ] using hi)
    have hcw : ∀ i, ContinuousOn (fun x => w x i) K := by
      intro i
      cases i with
      | zero => exact hop
      | succ j => exact hcont j
    exact ih (fun z hz => hrat z (List.mem_cons_of_mem _ hz)) hw hcw hc.2

end
end krylov.Correction.Certificate
