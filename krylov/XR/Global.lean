import krylov.XR.ExecutionDescent
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Sequences

/-!
Article: main_krylov, thm:XR, global stationarity of the actual XR executor.
Use: telescope the proved accepted-step descent of the literal one-probe
algorithm, derive square summability and stationarity of every limit point.
Source: the standard descent/summability argument (Armijo globalization),
applied to actual cached function/gradient observations of `run`.
-/

namespace krylov.XR
noncomputable section
open Filter Set
open scoped InnerProductSpace NNReal Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual recursive execution preserves its true endpoint cache and
the original fixed safeguard constants. -/
theorem run_cache_constants (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S₀ : State E)
    (hf : S₀.value = f S₀.point) (hg : S₀.gradient = G S₀.point) (k : ℕ) :
    let S := run P dimension model f G S₀ k
    S.value = f S.point ∧ S.gradient = G S.point ∧
      S.descentConstant = S₀.descentConstant ∧ S.normConstant = S₀.normConstant := by
  induction k with
  | zero => exact ⟨hf, hg, rfl, rfl⟩
  | succ k ih =>
    have hc := outerAdvance_cache P dimension model f G
      (run P dimension model f G S₀ k) ih.1 ih.2.1
    have hs := outerAdvance_constants P dimension model f G (run P dimension model f G S₀ k)
    exact ⟨hc.1, hc.2, hs.1.trans ih.2.2.1, hs.2.trans ih.2.2.2⟩

/-- Uniform accepted-step decrease along the actual recursive trajectory. -/
theorem run_sufficient_decrease (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hsigma : 0 < P.armijo) (hsigma₁ : P.armijo < 1) (S₀ : State E)
    (hc₁ : 0 < S₀.descentConstant) (hc₂ : S₀.descentConstant ≤ S₀.normConstant)
    (hf : S₀.value = f S₀.point) (hg : S₀.gradient = G S₀.point) (k : ℕ) :
    (run P dimension model f G S₀ (k+1)).value ≤
      (run P dimension model f G S₀ k).value -
        (P.armijo * minimumLength P.armijo S₀.descentConstant S₀.normConstant L *
          S₀.descentConstant) * ‖G (run P dimension model f G S₀ k).point‖ ^ 2 := by
  have hc := run_cache_constants P dimension model f G S₀ hf hg k
  have hd := outerAdvance_sufficient_decrease P dimension model f G hF L hL hG
    hsigma hsigma₁ (run P dimension model f G S₀ k)
    (by rwa [hc.2.2.1]) (by rwa [hc.2.2.1, hc.2.2.2]) hc.1 hc.2.1
  simpa only [run, hc.2.2.1, hc.2.2.2, hc.2.1] using hd

/-- Standard scalar telescope, used only after deriving the actual
executor's uniform sufficient decrease. -/
theorem descent_square_summable (v a : ℕ → ℝ) (c b : ℝ) (hc : 0 < c)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, b ≤ v k)
    (hd : ∀ k, v (k+1) ≤ v k - c * a k) : Summable a := by
  have ht (N : ℕ) : c * ∑ k ∈ Finset.range N, a k ≤ v 0 - v N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hd N]
  apply summable_of_sum_range_le (c := (v 0 - b) / c) ha
  intro N
  apply (le_div_iff₀ hc).2
  have h := ht N
  nlinarith [hb N]

/-- Genuine XR gradients are square summable whenever the objective is
bounded below. The model may be any data-only implementation, because
globalization is already part of the actual executor. -/
theorem run_gradient_square_summable (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hsigma : 0 < P.armijo) (hsigma₁ : P.armijo < 1) (S₀ : State E)
    (hc₁ : 0 < S₀.descentConstant) (hc₂ : S₀.descentConstant ≤ S₀.normConstant)
    (hf : S₀.value = f S₀.point) (hg : S₀.gradient = G S₀.point)
    (hb : ∃ b, ∀ x, b ≤ f x) :
    Summable (fun k => ‖G (run P dimension model f G S₀ k).point‖ ^ 2) := by
  obtain ⟨b, hb⟩ := hb
  have ht : 0 < minimumLength P.armijo S₀.descentConstant S₀.normConstant L := by
    apply lt_min (by norm_num)
    have hc₂pos := hc₁.trans_le hc₂
    positivity
  apply descent_square_summable (fun k => (run P dimension model f G S₀ k).value)
    _ (P.armijo * minimumLength P.armijo S₀.descentConstant S₀.normConstant L *
      S₀.descentConstant) b (mul_pos (mul_pos hsigma ht) hc₁)
    (fun _ => sq_nonneg _)
  · intro k
    rw [(run_cache_constants P dimension model f G S₀ hf hg k).1]
    exact hb _
  · exact run_sufficient_decrease P dimension model f G hF L hL hG hsigma hsigma₁
      S₀ hc₁ hc₂ hf hg

omit [InnerProductSpace ℝ E] in
/-- Square summability of true gradients implies their norm tends to zero. -/
theorem gradient_norm_tendsto_zero (x : ℕ → E) (G : E → E)
    (h : Summable (fun k => ‖G (x k)‖ ^ 2)) :
    Tendsto (fun k => ‖G (x k)‖) atTop (𝓝 0) := by
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp h.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht

omit [InnerProductSpace ℝ E] in
/-- Every subsequential limit is stationary. Convergence of the iterates
is not assumed in the global theorem. -/
theorem stationary_of_limit (x : ℕ → E) (G : E → E) (hG : Continuous G)
    (h : Summable (fun k => ‖G (x k)‖ ^ 2)) (z : E) (indices : ℕ → ℕ)
    (hi : Tendsto indices atTop atTop) (hx : Tendsto (x ∘ indices) atTop (𝓝 z)) :
    G z = 0 := by
  have hn := (gradient_norm_tendsto_zero x G h).comp hi
  have hz := (hG.norm.continuousAt.tendsto.comp hx)
  have he : ‖G z‖ = 0 := tendsto_nhds_unique hz hn
  exact norm_eq_zero.mp he

end
end krylov.XR
