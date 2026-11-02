import krylov.Stability.UniformGradient
import krylov.Methods.ExecutedProbed

/-!
Article: main_krylov, thm:UCq and apD:lem-step, genuine observed-gradient stability.
Use: Extend the uniform accumulated-gradient estimate to correction-contaminated
secants of actual probed methods without replacing them by exact operator images.
Source: actual consecutive-gradient secants, finite telescoping and norm bounds.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant
open scoped BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The genuine observed-secant and reference-step recurrences give their exact finite gradient-error allowance.
Use: Derive actual ordinary-RFC gradient stability without assuming an exact secant model.
Article: main_krylov, thm:UCq and apD:lem-step.
Proof: Subtract consecutive real updates, split into the previous gradient error, true step error and observed pair error, then induct over the actual finite sum.
-/
theorem observed_gradient_difference_bound (G G₀ s s₀ y : ℕ → E)
    (hinit : G 0=G₀ 0) (hG : ∀ i, G (i+1)=G i+y i)
    (hG₀ : ∀ i, G₀ (i+1)=G₀ i+s₀ i) (N : ℕ) :
    ‖G N-G₀ N‖≤∑ i ∈ range N, (‖s i-s₀ i‖+‖y i-s i‖) := by
  induction N with
  | zero => simp only [hinit,sub_self,norm_zero,sum_range_zero,le_refl]
  | succ N ih =>
    have he : G (N+1)-G₀ (N+1)=(G N-G₀ N)+(s N-s₀ N)+(y N-s N) := by
      rw [hG,hG₀]; abel
    rw [he,sum_range_succ]
    exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))).trans
      (by linarith)

omit [NormedSpace ℝ E] in
/-- Uniform real step and relative observed-secant errors control the actual accumulated gradient with a horizon-only coefficient.
Use: Derive actual ordinary-RFC gradient stability without assuming an exact secant model.
Article: main_krylov, thm:UCq and apD:lem-step.
Proof: The true reference step has norm at most one. Its actual step error bounds the observed step norm by C+1, and the exact finite gradient estimate counts these genuine errors.
-/
theorem observed_gradient_uniform_bound (G G₀ s s₀ y : ℕ → E)
    (hinit : G 0=G₀ 0) (hG : ∀ i, G (i+1)=G i+y i)
    (hG₀ : ∀ i, G₀ (i+1)=G₀ i+s₀ i) (N : ℕ) {δ C K : ℝ}
    (hδ : 0≤δ) (hδone : δ≤1) (hC : 0≤C) (hK : 0≤K)
    (href : ∀ i<N, ‖s₀ i‖≤1) (hs : ∀ i<N, ‖s i-s₀ i‖≤C*δ)
    (hy : ∀ i<N, ‖y i-s i‖≤K*δ*‖s i‖) :
    ‖G N-G₀ N‖≤(N : ℝ)*(C+K*(C+1))*δ := by
  apply (observed_gradient_difference_bound G G₀ s s₀ y hinit hG hG₀ N).trans
  calc
    _ ≤ ∑ _i ∈ range N, (C+K*(C+1))*δ := by
      apply sum_le_sum
      intro i hi
      have hiN := mem_range.mp hi
      have hsn := (norm_le_norm_sub_add (s i) (s₀ i)).trans (add_le_add (hs i hiN) (href i hiN))
      have hsc : ‖s i‖≤C+1 := hsn.trans (by nlinarith)
      have hb := (hy i hiN).trans (mul_le_mul_of_nonneg_left hsc (mul_nonneg hK hδ))
      nlinarith [hs i hiN]
    _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]; ring

variable {n : ℕ}

/-- Every actual probed trajectory has a uniform canonical gradient bound from its own true step and observed-secant errors.
Use: Derive actual ordinary-RFC gradient stability without assuming an exact secant model.
Article: main_krylov, thm:UCq and apD:lem-step.
Proof: Use the implemented consecutive-gradient secant identity, map the real updates through the inverse metric root and apply the proved observed finite accumulation bound. True CG energy monotonicity supplies the reference step bound.
-/
theorem probed_canonical_gradient_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {δ C K : ℝ}
    (hδ : 0≤δ) (hδone : δ≤1) (hC : 0≤C) (hK : 0≤K)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hs : ∀ i<N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)-
      canonicalCGStep base g i‖≤C*δ)
    (hy : ∀ i<N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedSecant m A B g i)-
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖≤
      K*δ*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedGradient m A B g N)-cgCanonicalError base g N‖≤
      (N : ℝ)*(C+K*(C+1))*δ := by
  apply observed_gradient_uniform_bound
    (fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedGradient m A B g i))
    (cgCanonicalError base g)
    (fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i))
    (canonicalCGStep base g)
    (fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedSecant m A B g i))
    rfl _ (cgCanonicalError_succ base hb g) N hδ hδone hC hK
    (fun i _ => (canonicalCGStep_norm_le_initial base hb g i).trans hinit) hs hy
  intro i
  simp only [probedSecant,map_sub]
  abel

end
end krylov.Stability
