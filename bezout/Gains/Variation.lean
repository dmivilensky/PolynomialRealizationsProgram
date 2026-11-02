import bezout.History.Oracle
import bezout.Synthesis.Exactness
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: bezout, Theorem 4.1 and Equation `eq:AN`.
Use: the insertion formula is the derivative of an actual causal execution
with the Hessian at call `s` changed to `H+t E_s`.
Proof: differentiate the finite triangular oracle equations. The derivative
itself is a physical execution with zero initial state and nominal-query
forcing; the exact additive response then gives the separated kernel.
-/

namespace bezout.History
noncomputable section
open Polynomial Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The physical oracle whose Hessian varies independently at each call. -/
def perturbedOracle (H : E →ₗ[ℝ] E) (D : Fin N → E →ₗ[ℝ] E) (t : ℝ)
    (s : Fin N) (v : E) : E := H v + t • D s v

/-- The first variation is forced by perturbations acting on nominal queries. -/
def variationNoise (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (D : Fin N → E →ₗ[ℝ] E) (initial : E) (s : Fin N) : E :=
  D s ((aeval H (h.query s)) initial)

/-- The output derivative, expressed using the actual physical response operators. -/
def firstVariation (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (D : Fin N → E →ₗ[ℝ] E) (initial : E) : E :=
  ∑ s, (aeval H (h.response s)) (h.variationNoise H D initial s)

omit [FiniteDimensional ℝ E] in
/-- At zero perturbation the actual query is the nominal polynomial query. -/
theorem perturbed_query_zero (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (D : Fin N → E →ₗ[ℝ] E) (initial : E) (s : Fin N) :
    h.oracleQuery initial (perturbedOracle H D 0) s = (aeval H (h.query s)) initial := by
  have ho : perturbedOracle H D 0 = fun _ v => H v + (0 : E) := by
    funext j v
    simp [perturbedOracle]
  rw [ho]
  exact h.nominal_query H initial (h.oracleExecution H initial (fun _ => 0)) s

/-- Differentiate every actual answer, retaining the complete causal dependence. -/
theorem hasDerivAt_perturbed_answer (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (D : Fin N → E →ₗ[ℝ] E) (initial : E) (s : Fin N) :
    HasDerivAt (fun t => h.oracleAnswers initial (perturbedOracle H D t) s)
      ((h.run H 0 (h.variationNoise H D initial)).answer s) 0 := by
  let v := h.run H 0 (h.variationNoise H D initial)
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    have hs (j : Fin N) : HasDerivAt
        (fun t => h.a s j • h.oracleAnswers initial (perturbedOracle H D t) j)
        (h.a s j • v.answer j) 0 := by
      by_cases hj : j < s
      · exact (ih j hj).const_smul _
      · simp only [h.triangular s j (le_of_not_gt hj), zero_smul]
        exact hasDerivAt_const 0 0
    have hq : HasDerivAt (fun t => h.oracleQuery initial (perturbedOracle H D t) s)
        (v.query s) 0 := by
      have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hs j)
      have hsub := (hasDerivAt_const 0 initial).sub hsum
      convert hsub using 1
      · funext t
        rfl
      · rw [v.query_eq]
    have hh := H.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hq
    have he := (D s).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hq
    have hp := hh.add ((hasDerivAt_id 0).smul he)
    have hder : H (v.query s) +
        ((0 : ℝ) • D s (v.query s) + (1 : ℝ) •
          D s (h.oracleQuery initial (perturbedOracle H D 0) s)) = v.answer s := by
      simp only [zero_smul, one_smul, zero_add, h.perturbed_query_zero H D initial s]
      exact (v.answer_eq s).symm
    change HasDerivAt
      (fun t => H (h.oracleQuery initial (perturbedOracle H D t) s) +
        t • D s (h.oracleQuery initial (perturbedOracle H D t) s))
      (H (v.query s) + ((0 : ℝ) • D s (v.query s) + (1 : ℝ) •
        D s (h.oracleQuery initial (perturbedOracle H D 0) s))) 0 at hp
    rw [hder] at hp
    apply hp.congr_of_eventuallyEq
    exact Eventually.of_forall fun t => h.oracleAnswers_eq initial _ s

/-- The article's separated insertion sum is the derivative of the actual
variable-Hessian oracle terminal, rather than a formal surrogate. -/
theorem hasDerivAt_perturbed_output (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (D : Fin N → E →ₗ[ℝ] E) (initial : E) :
    HasDerivAt (fun t => h.oracleOutput initial (perturbedOracle H D t))
      (h.firstVariation H D initial) 0 := by
  let v := h.run H 0 (h.variationNoise H D initial)
  have hs (s : Fin N) := (h.hasDerivAt_perturbed_answer H D initial s).const_smul (h.b s)
  have hd := (hasDerivAt_const 0 initial).sub
    (HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => hs s))
  have he : -∑ s, h.b s • v.answer s = h.firstVariation H D initial := by
    have hr := h.physical_response H 0 (h.variationNoise H D initial) v
    simpa only [Execution.output, map_zero, zero_sub, zero_add, firstVariation] using hr
  convert hd using 1
  · funext t
    rfl
  · rw [zero_sub]
    exact he.symm

end
end bezout.History
