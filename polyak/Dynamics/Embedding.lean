import polyak.Functions.Embedding
import polyak.Dynamics.UnitScale

/-!
Article: extension of a genuine example to larger dimensions.
Use: actual objective extensions and actual from-rest trajectories give
monotonicity of the finite-dimensional worst-case suprema.
-/

noncomputable section

namespace polyak.Dynamics

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Article: dimension extension of actual heavy-ball trajectories.
Proof: one step commutes with the linear embedding, preserving the zero momentum. -/
theorem iterate_embedding (J : E →ₗᵢ[ℝ] F) (g : E → E) (h : F → F)
    (hgrad : ∀ x, h (J x) = J (g x)) (α β : ℝ) (x₀ : E) (n : ℕ) :
    iterate h α β (J x₀) n = J (iterate g α β x₀ n) := by
  have hs : ∀ n, state h α β (J x₀) n =
      (J (state g α β x₀ n).1, J (state g α β x₀ n).2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [state, ih, step, hgrad, map_sub, map_add, map_smul]
  exact congrArg Prod.fst (hs n)

/-- Article: a smaller-dimensional source ratio is realized by a genuine
objective in d+k Euclidean dimensions, with exactly the same actual trajectory
norms. Proof: center at the actual minimizer, extend the normalized potential by
orthogonal projection, and embed the implemented run. -/
theorem ratio_embedding {μ L α β r : ℝ} {d N : ℕ}
    (hr : r ∈ ratios μ L α β d N) (k : ℕ) :
    r ∈ ratios μ L α β (d + k) N := by
  obtain ⟨f, hf, a, x₀, hmin, hne, hr⟩ := hr
  let J := euclideanInclusion d k
  let f₀ := centerObjective f a
  have hf₀ : CenteredSmoothStronglyConvex μ L f₀ := by
    refine ⟨hf.centerObjective a, ?_, ?_⟩
    · simp [f₀, centerObjective]
    · rw [(hasGradientAt_centerObjective hf.differentiable a 0).gradient]
      simpa using (hf.minimizer_iff a).mp hmin
  let G := extendObjective μ L J f₀
  have hG : CenteredSmoothStronglyConvex μ L G := hf₀.extendObjective J
  have hminG : ∀ y, G 0 ≤ G y :=
    (hG.toSmoothStronglyConvex.minimizer_iff 0).mpr hG.gradient_zero
  have hneG : J (x₀ - a) ≠ 0 := by
    intro hh
    have hz : x₀ - a = 0 := J.injective (hh.trans (map_zero J).symm)
    exact hne (sub_eq_zero.mp hz)
  have hrun := iterate_embedding J (gradient f₀) (gradient G)
    (gradient_extendObjective_embed hf₀.toSmoothStronglyConvex J) α β (x₀ - a) N
  have htranslate := iterate_translate (gradient f) (gradient f₀) a α β
    (fun e => (hasGradientAt_centerObjective hf.differentiable a e).gradient.symm) (x₀ - a) N
  simp only [add_sub_cancel] at htranslate
  refine ⟨G, hG.toSmoothStronglyConvex, 0, J (x₀ - a), hminG, hneG, ?_⟩
  rw [sub_zero, hrun, J.norm_map, sub_zero, J.norm_map]
  rw [htranslate, add_sub_cancel_left] at hr
  exact hr

/-- Article: source admissible ratio sets grow with ambient Euclidean dimension.
Proof: every witness is replaced by the explicit genuine extended objective. -/
theorem ratios_subset_add (μ L α β : ℝ) (d k N : ℕ) :
    ratios μ L α β d N ⊆ ratios μ L α β (d + k) N :=
  fun _ hr => ratio_embedding hr k

/-- Article: finite-dimensional worst cases are monotone under adding coordinates.
Proof: source ratio-set inclusion and the previously proved finite upper bound. -/
theorem worst_le_worst_add {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (d k N : ℕ) :
    worst μ L α β d N ≤ worst μ L α β (d + k) N := by
  apply csSup_le_csSup (ratios_bddAbove hμ hL hα hβ (d + k) N) (Set.insert_nonempty _ _)
  exact Set.insert_subset_insert (ratios_subset_add μ L α β d k N)

/-- Article: dimension monotonicity in the original Euclidean models.
Proof: write D as d plus the number of added coordinates. -/
theorem worst_mono_dimension {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) {d D : ℕ} (hdD : d ≤ D) (N : ℕ) :
    worst μ L α β d N ≤ worst μ L α β D N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdD
  exact worst_le_worst_add hμ hL hα hβ d k N

end polyak.Dynamics
