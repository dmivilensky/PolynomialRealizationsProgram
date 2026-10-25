import polyak.Dynamics.WorstCase
import polyak.Functions.Normalization
import polyak.Dynamics.Normalization

/-!
Article: polyaksiopt, eq:WN and Lemma normalization.
Use: nonempty actual problem classes, exact zero-horizon suprema and the
true normalized-gradient dictionary for the executor.
-/

namespace polyak.Dynamics
noncomputable section
open Set

/-- Article: eq:WN. Use: actual admissible instances exist in every positive dimension. -/
theorem ratios_nonempty {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (α β : ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ) : (ratios μ L α β d N).Nonempty := by
  let E := EuclideanSpace ℝ (Fin d)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let f : E → ℝ := denormalizeFunction μ L (fun _ => 0)
  have hf : CenteredSmoothStronglyConvex μ L f :=
    (normalizedSmooth_zero (E := E)).denormalize hμ hL
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  have hmin (y : E) : f 0 ≤ f y := by
    have h := hf.tangent_lower 0 y
    rw [hf.gradient_zero] at h
    simp only [inner_zero_left, sub_zero] at h
    have : 0 ≤ μ/2 * ‖y‖^2 := by positivity
    linarith
  exact ⟨_, f, hf.toSmoothStronglyConvex, 0, x₀, hmin, hx₀, rfl⟩

/-- Article: eq:WN. Use: insertion of zero does not change the source supremum. -/
theorem worst_eq_source_sup {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    worst μ L α β d N = sSup (ratios μ L α β d N) := by
  have hb : BddAbove (ratios μ L α β d N) :=
    (ratios_bddAbove hμ hL hα hβ d N).mono (subset_insert _ _)
  obtain ⟨r, hr⟩ := ratios_nonempty hμ hL α β hd N
  have hn : 0 ≤ sSup (ratios μ L α β d N) :=
    (ratio_nonneg hr).trans (le_csSup hb hr)
  exact (csSup_insert hb ⟨r, hr⟩).trans (max_eq_right hn)

/-- Article: eq:WN. Use: the normalized ratio at horizon zero is one. -/
theorem ratio_zero_eq_one {μ L α β r : ℝ} {d : ℕ}
    (hr : r ∈ ratios μ L α β d 0) : r = 1 := by
  obtain ⟨f, _, xstar, x₀, _, hne, rfl⟩ := hr
  simp only [iterate_zero]
  exact div_self (norm_ne_zero_iff.2 (sub_ne_zero.2 hne))

/-- Article: eq:WN. Use: no empty-supremum convention affects the initial horizon. -/
theorem worst_zero {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) {d : ℕ} (hd : 0 < d) :
    worst μ L α β d 0 = 1 := by
  apply le_antisymm (by simpa using worst_le hμ hL hα hβ d 0)
  obtain ⟨r, hr⟩ := ratios_nonempty hμ hL α β hd 0
  have hr1 := ratio_zero_eq_one hr
  rw [← hr1]
  exact le_csSup (ratios_bddAbove hμ hL hα hβ d 0) (mem_insert_of_mem _ hr)

/-- Article: eq:WN. Use: the dimension-uniform initial worst case is one. -/
theorem worstAll_zero {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : worstAll μ L α β 0 = 1 := by
  apply le_antisymm (by simpa using worstAll_le hμ hL hα hβ 0)
  calc
    1 = worst μ L α β 1 0 := (worst_zero hμ hL hα hβ (by norm_num)).symm
    _ ≤ _ := worst_le_worstAll hμ hL hα hβ (by norm_num) 0

/-- Article: lem:normalization. Use: genuine normalized functions drive the actual run. -/
theorem denormalized_error_state {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ψ : E → ℝ}
    (hψ : NormalizedSmooth ψ) (μ L α β : ℝ) (e₀ : E) (n : ℕ) :
    state (gradient (denormalizeFunction μ L ψ)) α β e₀ n =
      normalizedState (gradient ψ) (normalizedA μ L α β) (normalizedB μ L α) β e₀ n := by
  have h := normalized_error_state (gradient (denormalizeFunction μ L ψ))
    (gradient ψ) μ L α β 0 e₀ (fun e => by
      simpa using (hasGradientAt_denormalize hψ.differentiable e).gradient) n
  simpa using h

end
end polyak.Dynamics
