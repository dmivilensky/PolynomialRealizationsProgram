import krylov.Functions.SelfConcordantRadiusExpansion
import krylov.Functions.SelfConcordantLipschitz
import krylov.Functions.MidpointExpansion

/-!
Article: main_krylov, apG:sc(iii,iv), actual self-concordant secants.
Use: assemble the sharp Hessian bound with the actual secant integral and
its uniform midpoint expansion. The third derivative has true norm at most
two at the canonically normalized centre.
Source: Nesterov18, Lemma 5.1.2 and Theorem 5.1.7; actual Frechet
differentiability and the proved segment integral comparison.
-/

namespace krylov.Functions
noncomputable section
open Set Metric
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual third derivative at a canonical self-concordant centre has norm at most two.
Article: main_krylov, apG:sc(iv).
Proof: the genuine mixed differential inequality at the identity Hessian
bounds the actual derivative operator directly. -/
theorem standardSelfConcordant_third_norm (f : E → ℝ) (U : Set E)
    (D : krylov.Nonlinear.StandardSelfConcordantData f U)
    (h₀ : (0 : E) ∈ U) (hH₀ : D.hessian 0 = ContinuousLinearMap.id ℝ E) :
    ‖D.variation 0‖ ≤ 2 := by
  have h := krylov.Nonlinear.selfConcordant_mixed_derivative_norm_le
    (D.hessian 0) (D.variation 0) (D.mixed 0 h₀) (by norm_num : (0 : ℝ) ≤ 1)
    (by rw [hH₀]; simpa using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
  simpa using h

/-- True self-concordant secants have a common little-o midpoint expansion.
Article: main_krylov, apG:sc(iv).
Proof: the genuine scalar-function differential data provide the actual
Hessian derivative and an enclosing open ball; apply the uniform integral
expansion with that actual derivative. -/
theorem standardSelfConcordant_midpoint_expansion (f : E → ℝ) (U : Set E)
    (D : krylov.Nonlinear.StandardSelfConcordantData f U)
    (h₀ : (0 : E) ∈ U) (hH₀ : D.hessian 0 = ContinuousLinearMap.id ℝ E) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ R : ℝ, 0 ≤ R → R < δ → ∀ a u : E,
      (∀ t ∈ Icc (0 : ℝ) 1, ‖a + t • u‖ ≤ R) →
      ‖chebyshev1.Nonlinear.averagedDerivative D.hessian a u -
        ContinuousLinearMap.id ℝ E - D.variation 0 (a + (1 / 2 : ℝ) • u)‖ ≤ ε * R := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp D.open_domain 0 h₀
  have hc : ContinuousOn D.hessian (ball 0 r) :=
    fun x hx => (D.hessian_derivative x (hball hx)).continuousAt.continuousWithinAt
  intro ε hε
  obtain ⟨δ, hδ, _, hbound⟩ := averagedHessian_midpoint_expansion
    D.hessian (D.variation 0) hr hc (D.hessian_derivative 0 h₀) ε hε
  refine ⟨δ, hδ, ?_⟩
  simpa only [hH₀] using hbound

end
end krylov.Functions
