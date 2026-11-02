import krylov.OneGradient.InformedExactQueries
import krylov.OneGradient.HiddenPlaneCentre
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), genuine history-only known-base centring.
Use: implement the original two-dimensional minimax attaining candidate
as an actual M1 method with two evaluated queries and no output query.
Source: real informed query executor, genuine known reference CG frame,
actual returned gradient and the observed hidden-entry interval midpoint.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The actual known-base two-dimensional observed-column centre output.
All inputs are the known fixed reference, known total increment allowance,
the initial gradient and actual returned gradient in the real history.
Use: no unknown increment, hidden entry or actual operator is captured
by the attaining candidate's final decision.
Article: main_krylov, thm:local(c), genuine centred output rule. -/
def knownBaseCentreOutput (base : Matrix (Fin 2) (Fin 2) ℝ) (eta : ℝ)
    (H : History (EuclideanSpace ℝ (Fin 2))) : EuclideanSpace ℝ (Fin 2) :=
  let sigma := ‖canonicalCGStep base H.initial 1‖
  let rho := cgOperator (metricRoot base)⁻¹ H.gradient
  let column := (eta*sigma)⁻¹ • rho
  let e := canonicalCGUnitStep base H.initial 0
  let h := canonicalCGUnitStep base H.initial 1
  let a := inner ℝ e column
  let g := inner ℝ h column
  let J := 1+eta • planarMatrix e h (hiddenPlaneCentre a g) a g
  show EuclideanSpace ℝ (Fin 2) from -(cgOperator (metricRoot base)⁻¹ (cgOperator J⁻¹ rho))

/-- The genuine original two-query known-base centring method. Its actual
queries are informed XRFC queries; its final output is the actual
observed-column centre inverse correction computed from its real history.
Use: a concrete globally defined data-only M1 policy, not an abstract
minimax centre or an output formula using the unknown matrix.
Article: main_krylov, thm:local(c), attaining centring candidate. -/
def knownBaseCentredMethod (base : Matrix (Fin 2) (Fin 2) ℝ) (eta : ℝ) :
    OneGradientMethod (EuclideanSpace ℝ (Fin 2)) where
  step := (xrfcMethod fullMemory (informedTrial (cgOperator base))).step
  output := knownBaseCentreOutput base eta

/-- The original history-only centring candidate belongs to the true M1
source class on all histories, without positivity or full-atom premises.
Use: its attaining candidate's implementation satisfies the original
information restriction independently of the later approximation proof.
Article: main_krylov, thm:local(c), genuine method-class membership.
Proof: every actual evaluated query is exactly the already proved
observed-span-restricted informed full-memory XRFC query. -/
theorem knownBaseCentredMethod_spanRestricted (base : Matrix (Fin 2) (Fin 2) ℝ) (eta : ℝ) :
    OneGradientSpanRestricted (knownBaseCentredMethod base eta) :=
  xrfcMethod_spanRestricted fullMemory (informedTrial (cgOperator base))

/-- Every actually evaluated complete history of the original centring
candidate is exactly the real informed executor history on arbitrary
varying segment operators. The output spends no extra observed query.
Use: all native informed query identities transfer to the genuine M1
centred algorithm, rather than a substituted reference trajectory.
Article: main_krylov, thm:local(c), true centring execution dictionary.
Proof: induction through the actual record recursion; the two genuine
methods have exactly the same history-only evaluated decision field. -/
theorem knownBaseCentredMethod_histories (base : Matrix (Fin 2) (Fin 2) ℝ) (eta : ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (g : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    oneGradientRun (knownBaseCentredMethod base eta) A g k=
      oneGradientRun (xrfcMethod fullMemory (informedTrial (cgOperator base))) A g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change oneGradientAdvance (knownBaseCentredMethod base eta) (A k)
      (oneGradientRun (knownBaseCentredMethod base eta) A g k)=_
    rw [ih]
    rfl

/-- The genuine two-dimensional centring method uses exactly three
gradients: the initial observation and its two true evaluated queries.
Use: the final actual centre inverse is an unevaluated M1 output.
Article: main_krylov, thm:local(c), original gradient cost.
Proof: the exact original one-gradient executor cost theorem. -/
theorem knownBaseCentredMethod_cost (base : Matrix (Fin 2) (Fin 2) ℝ) (eta : ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (g : EuclideanSpace ℝ (Fin 2)) :
    oneGradientCost (oneGradientRun (knownBaseCentredMethod base eta) A g 2)=3 :=
  oneGradientCost_run _ _ _ _

end
end krylov.OneGradient
