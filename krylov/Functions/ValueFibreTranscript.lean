import krylov.Functions.ValueDataFibre
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Article: main_krylov, prop:Fcycle(iii), exact observation and search transcripts.
Use: pass from the proved cubic derivative to actual Riesz gradients, actual
line-search restrictions, and the printed final two-dimensional Hessian.
Source: Appendix G, the exact cubic fibre and elementary coordinate algebra.
-/

namespace krylov.Functions
noncomputable section
section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The hidden function vanishes identically on either observed search hyperplane.
Article: main_krylov, prop:Fcycle(iii), exact line-search indistinguishability. -/
theorem valueFibreCubic_search_hyperplanes (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E)
    (hx : ψ x = 0 ∨ φ x = p) : valueFibreCubic φ ψ d p r x = 0 := by
  rcases hx with hx | hx <;> simp [valueFibreCubic, hx]

/-- The entire first and last line-search objective restrictions agree exactly.
Article: main_krylov, prop:Fcycle(iii), including the method's exact line search.
Proof: both relevant affine lines lie in a hyperplane on which the perturbation is zero. -/
theorem add_valueFibreCubic_search_line (f : E → ℝ) (φ ψ : E →L[ℝ] ℝ)
    (d p r : ℝ) (a s : E)
    (hline : (ψ a = 0 ∧ ψ s = 0) ∨ (φ a = p ∧ φ s = 0)) :
    (fun t : ℝ => f (a + t • s) + valueFibreCubic φ ψ d p r (a + t • s)) =
      (fun t : ℝ => f (a + t • s)) := by
  ext t
  rw [valueFibreCubic_search_hyperplanes φ ψ d p r]
  · exact add_zero _
  · rcases hline with ⟨ha, hs⟩ | ⟨ha, hs⟩
    · left
      simp only [map_add, map_smul, ha, hs, smul_zero, add_zero]
    · right
      simp only [map_add, map_smul, ha, hs, smul_zero, add_zero]

/-- Actual step recurrences place every finite observed point at one of the three planar samples.
Article: main_krylov, prop:Fcycle(iii), the reference projected trajectory.
Proof: telescope both real linear coordinates, whose only increments are the first and last steps. -/
theorem valueFibre_coordinates_of_steps (N : ℕ) (hN : 0 < N) (x s : ℕ → E)
    (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (hstep : ∀ k < N, x (k + 1) = x k + s k)
    (hφ : ∀ k < N, φ (s k) = if k = 0 then p else 0)
    (hψ : ∀ k < N, ψ (s k) = if k + 1 = N then r * p else 0)
    {k : ℕ} (hk : k ≤ N) :
    φ (x k - x 0) = (if k = 0 then 0 else p) ∧
      ψ (x k - x 0) = (if k = N then r * p else 0) := by
  induction k with
  | zero => simp [Ne.symm (Nat.ne_of_gt hN)]
  | succ k ih =>
    have hkp : k < N := by omega
    have he : x (k + 1) - x 0 = (x k - x 0) + s k := by rw [hstep k hkp]; abel
    rw [he, map_add, map_add, (ih (by omega)).1, (ih (by omega)).2, hφ k hkp, hψ k hkp]
    constructor
    · by_cases hk₀ : k = 0 <;> simp [hk₀]
    · simp only [ne_of_lt hkp, ↓reduceIte, zero_add]

/-- The genuine final Hessian compresses to exactly the printed planar matrix.
Article: main_krylov, prop:Fcycle(iii).
Proof: evaluate the actual Hessian on the two dual coordinate directions. -/
theorem valueFibreHessian_final_matrix (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ)
    (x : E) (hφ : φ x = p) (hψ : ψ x = r * p) (e h : E)
    (hφe : φ e = 1) (hψe : ψ e = 0) (hφh : φ h = 0) (hψh : ψ h = 1) :
    let v : Fin 2 → E := ![e, h]
    compressBilinear v (valueFibreHessian φ ψ d p r x) =
      (p * d / 2) • !![-2 * r ^ 2, r; r, 0] := by
  dsimp only
  rw [valueFibreHessian_final φ ψ d p r x hφ hψ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compressBilinear, ContinuousLinearMap.smulRight_apply, hφe, hψe, hφh, hψh]

end Normed

section Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual Riesz gradients, as well as values, agree on every observed planar sample.
Article: main_krylov, prop:Fcycle(iii), exact value-gradient data fibre. -/
theorem add_valueFibreCubic_gradient (f : E → ℝ) (D : E →L[ℝ] ℝ)
    (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) (hf : HasFDerivAt f D x)
    (hx : (φ x = 0 ∧ ψ x = 0) ∨ (φ x = p ∧ ψ x = 0) ∨
      (φ x = p ∧ ψ x = r * p)) :
    gradient (fun y => f y + valueFibreCubic φ ψ d p r y) x = gradient f x := by
  unfold gradient
  rw [(add_valueFibreCubic_sample f D φ ψ d p r x hf hx).2.fderiv, hf.fderiv]

/-- The entire actual finite value-gradient transcript is independent of the hidden cubic coefficient.
Article: main_krylov, prop:Fcycle(iii), all first, intermediate and last observed points.
Proof: the real step recurrences give the three projected coordinates; translate
the proved vanishing derivative, then identify the actual Riesz gradients. -/
theorem valueFibreCubic_value_gradient_transcript (N : ℕ) (hN : 0 < N) (x s : ℕ → E)
    (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ)
    (hstep : ∀ k < N, x (k + 1) = x k + s k)
    (hφ : ∀ k < N, φ (s k) = if k = 0 then p else 0)
    (hψ : ∀ k < N, ψ (s k) = if k + 1 = N then r * p else 0)
    (f : E → ℝ) (hf : ∀ k ≤ N, DifferentiableAt ℝ f (x k)) :
    ∀ k ≤ N,
      f (x k) + valueFibreCubic φ ψ d p r (x k - x 0) = f (x k) ∧
        gradient (fun y => f y + valueFibreCubic φ ψ d p r (y - x 0)) (x k) =
          gradient f (x k) := by
  intro k hk
  have hc := valueFibre_coordinates_of_steps N hN x s φ ψ p r hstep hφ hψ hk
  have hcoords : (φ (x k - x 0) = 0 ∧ ψ (x k - x 0) = 0) ∨
      (φ (x k - x 0) = p ∧ ψ (x k - x 0) = 0) ∨
      (φ (x k - x 0) = p ∧ ψ (x k - x 0) = r * p) := by
    by_cases hk₀ : k = 0
    · left
      simp only [hk₀, sub_self, map_zero, and_self]
    by_cases hkN : k = N
    · right; right
      exact ⟨by simpa only [hk₀, ↓reduceIte] using hc.1,
        by simpa only [hkN, ↓reduceIte] using hc.2⟩
    · right; left
      simpa only [hk₀, hkN, ↓reduceIte] using hc
  have hz := valueFibreCubic_sample_zero φ ψ d p r (x k - x 0) hcoords
  have ht : HasFDerivAt (fun y => valueFibreCubic φ ψ d p r (y - x 0))
      (0 : E →L[ℝ] ℝ) (x k) := by
    simpa only [ContinuousLinearMap.zero_comp] using!
      hz.2.comp (x k) ((hasFDerivAt_id (x k)).sub_const (x 0))
  constructor
  · rw [hz.1, add_zero]
  · have hsum : HasFDerivAt (fun y => f y + valueFibreCubic φ ψ d p r (y - x 0))
        (fderiv ℝ f (x k)) (x k) := by
      simpa only [add_zero] using! (hf k hk).hasFDerivAt.add ht
    unfold gradient
    rw [hsum.fderiv]

end Gradient
end
end krylov.Functions
