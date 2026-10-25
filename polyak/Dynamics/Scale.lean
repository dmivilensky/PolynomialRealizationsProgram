import polyak.Dynamics.Rate
import polyak.Functions.Transforms

/-!
Article: normalization of curvature scale in the first part.
Use: positive rescaling preserves the actual trajectory and all worst-case ratios.
-/

namespace polyak.Dynamics
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Article: eq:hb. Use: simultaneous gradient/step rescaling leaves the actual executor equal. -/
theorem state_scale_gradient (g : E → E) (α β c : ℝ) (hc : c ≠ 0) (x₀ : E) (n : ℕ) :
    state (fun x => c • g x) (α/c) β x₀ n = state g α β x₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [state, ih, step, smul_smul, div_mul_cancel₀ α hc]

/-- Article: eq:hb. Use: actual position invariance under a positive objective scaling. -/
theorem iterate_scale_gradient (g : E → E) (α β c : ℝ) (hc : c ≠ 0) (x₀ : E) (n : ℕ) :
    iterate (fun x => c • g x) (α/c) β x₀ n = iterate g α β x₀ n :=
  congrArg Prod.fst (state_scale_gradient g α β c hc x₀ n)

/-- Article: eq:WN. Use: source instances remain actual functions after rescaling. -/
theorem ratio_scale {μ L α β r c : ℝ} (hc : 0 < c) {d N : ℕ}
    (hr : r ∈ ratios μ L α β d N) : r ∈ ratios (c*μ) (c*L) (α/c) β d N := by
  obtain ⟨f, hf, xstar, x₀, hmin, hne, hr⟩ := hr
  have hgrad : gradient (fun x => c*f x) = fun x => c • gradient f x := by
    apply gradient_eq
    intro x
    simpa using hasGradientAt_quadratic_add (hf.differentiable x).hasGradientAt 0 c
  refine ⟨fun x => c*f x, hf.mul_pos hc, xstar, x₀,
    fun y => mul_le_mul_of_nonneg_left (hmin y) hc.le, hne, ?_⟩
  rw [hgrad, iterate_scale_gradient _ _ _ _ (ne_of_gt hc)]
  exact hr

/-- Article: eq:WN. Use: rescaling is an equality of original admissible ratio sets. -/
theorem ratios_scale {μ L α β c : ℝ} (hc : 0 < c) (d N : ℕ) :
    ratios (c*μ) (c*L) (α/c) β d N = ratios μ L α β d N := by
  ext r
  constructor
  · intro hr
    have h := ratio_scale (inv_pos.2 hc) hr
    simpa [ne_of_gt hc, div_eq_mul_inv] using h
  · exact ratio_scale hc

/-- Article: eq:WN. Use: every finite-dimensional worst-case value is scale invariant. -/
theorem worst_scale {μ L α β c : ℝ} (hc : 0 < c) (d N : ℕ) :
    worst (c*μ) (c*L) (α/c) β d N = worst μ L α β d N := by
  simp only [worst, ratios_scale hc]

/-- Article: eq:WN. Use: the dimension-uniform worst case preserves curvature scaling. -/
theorem worstAll_scale {μ L α β c : ℝ} (hc : 0 < c) (N : ℕ) :
    worstAll (c*μ) (c*L) (α/c) β N = worstAll μ L α β N := by
  simp only [worstAll, allRatios, ratios_scale hc]

/-- Article: eq:WN. Use: the true limsup factor is scale invariant. -/
theorem rate_scale {μ L α β c : ℝ} (hc : 0 < c) :
    rate (c*μ) (c*L) (α/c) β = rate μ L α β := by
  simp only [rate, worstAll_scale hc]

end
end polyak.Dynamics
