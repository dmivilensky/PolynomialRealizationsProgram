import krylov.Methods.DirectionInformation
import krylov.Methods.ObservedRules
import krylov.Methods.RFC
import krylov.Realization.FixedBridge

/-!
Article: Definition 2.5 [def:classes] of krylov.tex.
Use: package the source's exact information restrictions separately from
quadratic consistency and smooth observed-coefficient rules. The raw protocols
remain available for information lower bounds in larger classes.
Source: the article's definitions, actual observed-span proofs and the reused
finite-memory affine realizations of PasechnyukTakac26.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A fixed finite-memory oblivious realization with the true source normalization.
Use: coefficients are fixed prior data, independently of every future observation.
Article: main_krylov, def:classes(O). -/
structure ObliviousClass (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The actual fixed affine memory transition and scalar query/readout data. -/
  realization : chebyshev1.Realization ι
  /-- Constant-preserving actual scalar transfers, equivalently residual normalization. -/
  normalized : krylov.Realization.ObliviousNormalized realization

/-- An actual member of the source's one-gradient information class.
Use: the evaluated step lies in the real observed span; the output is a separate data-only unevaluated decision.
Article: main_krylov, def:classes(M₁). -/
structure OneGradientClass (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The real one-query step and separate unevaluated output policy. -/
  policy : OneGradientMethod E
  /-- Every evaluated step is a combination of genuinely observed vectors. -/
  admissible : OneGradientSpanRestricted policy

/-- An actual member of the source's probed information class with its prescribed stored window.
Use: directions obey the real observed span and every possible correction branch stays in the true augmented stored span.
Article: main_krylov, def:classes(M). -/
structure ProbedClass (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The prescribed data-independent pair-retention rule. -/
  memory : ℕ → ℕ
  /-- The genuinely nonanticipating direction and finite adaptive correction policy. -/
  policy : ProbedMethod E
  /-- Exact direction and all-branch correction-span information restrictions. -/
  admissible : ProbedSpanRestricted memory policy

/-- Actual FC, with any prescribed window, is a member of the exact probed information class.
Use: no quadratic or smoothness assumption is required for its information admissibility.
Article: main_krylov, def:classes and alg:fc. -/
def fcClass (memory : ℕ → ℕ) : ProbedClass E :=
  ⟨memory,fcMethod memory,fcMethod_spanRestricted memory⟩

/-- Actual repeated gated RFC is a member of the exact probed information class.
Use: every intermediate real gradient and every possible continuation satisfies the source's correction-span restriction.
Article: main_krylov, def:classes and alg:fc. -/
def rfcClass (memory : ℕ → ℕ) (count : ℕ) : ProbedClass E :=
  ⟨memory,rfcMethod memory count,rfcMethod_spanRestricted memory count⟩

/-- Actual step-basis XRFC with any data-only trial rule belongs to the exact one-gradient class.
Use: its final virtual output remains genuinely unevaluated.
Article: main_krylov, def:classes and alg:xrfc. -/
def xrfcClass (memory : ℕ → ℕ) (trial : History E → ℝ) : OneGradientClass E :=
  ⟨xrfcMethod memory trial,xrfcMethod_spanRestricted memory trial⟩

/-- Actual direction-basis XRFC-D belongs to the exact one-gradient class.
Use: replayed direction images are derived from real gradient differences rather than supplied by an extra oracle.
Article: main_krylov, def:classes and alg:xrfc-D. -/
def xrfcDClass (memory : ℕ → ℕ) (trial : History E → ℝ) : OneGradientClass E :=
  ⟨xrfcDMethod memory trial,xrfcDMethod_spanRestricted memory trial⟩

/-- The actual FC class member is globally CG-consistent for every newest-retaining memory.
Use: consistency and information membership are both proved properties of the same executed policy.
Article: main_krylov, def:classes and lem:consistent(a).
Proof: apply the already proved actual quadratic-transcript consistency theorem. -/
theorem fcClass_consistent (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) :
    CGConsistent (fcClass (E := E) memory).policy := fcMethod_consistent memory hm

/-- Every finite repeated RFC class member is globally CG-consistent for newest-retaining memory.
Use: all actual repeated corrections vanish on its genuine quadratic transcript.
Article: main_krylov, def:classes and lem:consistent(a).
Proof: use the actual retained-history and zero-correction consistency proof. -/
theorem rfcClass_consistent (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) (count : ℕ) :
    CGConsistent (rfcClass (E := E) memory count).policy := rfcMethod_consistent memory hm count

/-- Every source-normalized oblivious class member has residual value one at zero.
Use: normalization concerns the true polynomial constructed from the actual fixed-memory transitions.
Article: main_krylov, def:classes(O).
Proof: the existing scalar-transfer/polynomial bridge evaluates the actual normalization hypothesis. -/
theorem ObliviousClass.residual_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ObliviousClass ι) (k : ℕ) : (R.realization.residualPolynomial k).eval 0=1 :=
  krylov.Realization.oblivious_residual_zero R.realization R.normalized k

end
end krylov.Methods
