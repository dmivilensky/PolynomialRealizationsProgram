import nesterov.Flow.Run

/-!
Article: the literal logarithmic definition of ℓ in §3.
Use: a nonstationary solution never reaches the zero state, so the extended
log convention in the general exponent API agrees with the article's
ordinary real logarithm at every nonnegative time.
-/

noncomputable section

namespace nesterov.Flow

open Set Metric Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem IsSolution.state_nonzero {θ m : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hzero : ‖x 0‖ + ‖v 0‖ ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) : ‖x t‖ + ‖v t‖ ≠ 0 := by
  intro hstate
  have hx0 : x t = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (x t), norm_nonneg (v t)])
  have hv0 : v t = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (x t), norm_nonneg (v t)])
  let α := fun s => (x s, v s)
  let β := fun _ : ℝ => (0 : E × E)
  have hdα (s : ℝ) (hs : 0 ≤ s) : HasDerivAt α (vectorField θ f (α s)) s :=
    (hx.position_derivative s hs).prodMk (hx.velocity_derivative s hs)
  have hdβ (s : ℝ) : HasDerivAt β (vectorField θ f (β s)) s := by
    have hz : vectorField θ f (β s) = 0 := by simp [β, vectorField, hf.gradient_zero]
    rw [hz]
    exact hasDerivAt_const s (0 : E × E)
  have hcα : ContinuousOn α (Icc 0 t) := fun s hs => (hdα s hs.1).continuousAt.continuousWithinAt
  have hcβ : ContinuousOn β (Icc 0 t) := fun s _ => (hdβ s).continuousAt.continuousWithinAt
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E × E)).mp
    (((isCompact_Icc.image_of_continuousOn hcα).union
      (isCompact_Icc.image_of_continuousOn hcβ)).isBounded)
  obtain ⟨K, hK⟩ := hf.vectorField_lipschitz_bounded (θ := θ) R
  have heq := ODE_solution_unique_of_mem_Icc_left (v := fun _ => vectorField θ f)
    (s := fun _ => closedBall (0 : E × E) R) (fun _ _ => hK) hcα
    (fun s hs => (hdα s hs.1.le).hasDerivWithinAt)
    (fun s hs => hR (Or.inl ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩)) hcβ
    (fun s _ => (hdβ s).hasDerivWithinAt)
    (fun s hs => hR (Or.inr ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩))
    (show α t = β t by exact Prod.ext hx0 hv0) (by exact ⟨le_rfl, ht⟩)
  have heqx : x 0 = 0 := congrArg Prod.fst heq
  have heqv : v 0 = 0 := congrArg Prod.snd heq
  exact hzero (by simp [heqx, heqv])

/-- On all nonstationary actual runs, ℓ is exactly the article's logarithmic
liminf; no alternate asymptotic rate notion was substituted. -/
theorem IsSolution.decayExponent_eq_article {θ m : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) (hzero : ‖x 0‖ + ‖v 0‖ ≠ 0) :
    decayExponent x v = Filter.liminf
      (fun t : ℝ => ((-Real.log (‖x t‖ + ‖v t‖) / t : ℝ) : EReal)) Filter.atTop := by
  apply Filter.liminf_congr
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact ite_eq_right (hx.state_nonzero hf hzero ht)

/-- Initial nontriviality in `Run` is exactly the article's requirement that
the half-line solution is not the stationary zero solution. -/
theorem IsSolution.initial_zero_iff_stationary {θ m : ℝ} {f : E → ℝ} {x v : ℝ → E}
    (hf : Objective m f) (hx : IsSolution θ f x v) :
    ‖x 0‖ + ‖v 0‖ = 0 ↔ ∀ t : ℝ, 0 ≤ t → x t = 0 ∧ v t = 0 := by
  constructor
  · intro hz
    have hx0 : x 0 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (x 0), norm_nonneg (v 0)])
    have hv0 : v 0 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (x 0), norm_nonneg (v 0)])
    have hstationary : IsSolution θ f (fun _ => (0 : E)) (fun _ => (0 : E)) := by
      constructor
      · intro t _
        exact hasDerivAt_const t 0
      · intro t _
        have he : -θ • (0 : E) - gradient f 0 = 0 := by simp [hf.gradient_zero]
        rw [he]
        exact hasDerivAt_const t 0
    intro t ht
    exact hx.unique hf hstationary hx0 hv0 ht
  · intro hstationary
    obtain ⟨hx0, hv0⟩ := hstationary 0 le_rfl
    simp [hx0, hv0]

end nesterov.Flow
