import nesterov.Stationary.SourceDictionary
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Polynomial.Div

/-!
Article: Definition `def:second`.
Use: a second-order family is represented by its germ at ε=0 from the right.
Methods outside the original parameter interval may be extended arbitrarily;
all continuity and root assumptions below concern only that germ. The root β
is precisely the root in condition (ii), with its continuous value β₀=1. No
factorization, normal-form estimate, or root-convergence theorem is assumed.
-/
namespace nesterov.Slow
noncomputable section
open Filter Set Polynomial
open scoped Topology

structure SecondOrderFamily (θ y : ℝ) where
  method : ℝ → StationaryMethod
  memory : ℕ
  memory_two : 2 ≤ memory
  fixed_memory : ∀ ε,(method ε).memory=memory
  query_cont : ∀ j : ℕ,ContinuousWithinAt (fun ε=>((method ε).queryPolynomial).coeff j) (Ici 0) 0
  recurrence_cont : ∀ j : ℕ,ContinuousWithinAt (fun ε=>((method ε).recurrencePolynomial).coeff j) (Ici 0) 0
  theta_pos : 0<θ
  step_pos : 0<y
  q0 : Polynomial ℝ
  initial_factor : (method 0).recurrencePolynomial=(X-C 1)^2*q0
  q0_one : q0.eval 1= -1/y
  beta : ℝ→ℝ
  beta_zero : beta 0=1
  beta_root : ∀ᶠ ε in 𝓝[>] (0:ℝ),((method ε).recurrencePolynomial).eval (beta ε)=0
  beta_slow : Tendsto (fun ε=>(1-beta ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 θ)

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

abbrev u (ε : ℝ) : Polynomial ℝ := (F.method ε).queryPolynomial
abbrev v (ε : ℝ) : Polynomial ℝ := (F.method ε).recurrencePolynomial

def thetaAt (ε : ℝ) : ℝ := (1-F.beta ε)/ε

def quotient (ε : ℝ) : Polynomial ℝ :=
  (F.v ε /ₘ (X-C 1)) /ₘ (X-C (F.beta ε))

def stepAt (ε : ℝ) : ℝ := -1/(F.quotient ε).eval 1

/-- The original family regularity, restricted to the endpoint germ needed
by the asymptotic theorems. No regularity beyond continuity is implicit. -/
def CoeffCk (k : ℕ) : Prop :=
  (∀ j : ℕ,ContDiffWithinAt ℝ k (fun ε=>(F.u ε).coeff j) (Ici 0) 0) ∧
  (∀ j : ℕ,ContDiffWithinAt ℝ k (fun ε=>(F.v ε).coeff j) (Ici 0) 0)

@[simp] theorem u_one (ε : ℝ) : (F.u ε).eval 1=1 := by
  simp only [u,StationaryMethod.queryPolynomial,eval_finsetSum,eval_monomial,one_pow,mul_one]
  exact (F.method ε).query_sum

@[simp] theorem v_one (ε : ℝ) : (F.v ε).eval 1=0 := by
  simp only [v,StationaryMethod.recurrencePolynomial,eval_finsetSum,eval_monomial,one_pow,mul_one]
  exact (F.method ε).recurrence_sum

theorem v_natDegree (ε : ℝ) : (F.v ε).natDegree=F.memory := by
  rw [(F.method ε).recurrencePolynomial_natDegree,F.fixed_memory]

theorem u_natDegree_lt (ε : ℝ) : (F.u ε).natDegree<F.memory := by
  simpa only [F.fixed_memory] using (F.method ε).queryPolynomial_natDegree_lt

theorem thetaAt_tendsto : Tendsto F.thetaAt (𝓝[>] (0:ℝ)) (𝓝 θ) := F.beta_slow

end SecondOrderFamily
end
end nesterov.Slow
