import krylov.XR.Global
import krylov.Nonlinear.GradientLocal

/-!
Article: main_krylov, G1 and proof of thm:grow, actual query localization.
Use: derive O(e_k) bounds for every genuine first probe and reset/backtrack
query directly from the internal safeguard and the local true gradient.
No query enclosure is an execution field. Source: actual gradient-related
steps and the derivative mean-value theorem on a local convex ball.
-/

namespace krylov.XR
noncomputable section
open Set Metric
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real unchanged-anchor state passed to the second ModelStep after
the sole stored rejected probe. -/
def firstProbeState (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (S : State E) : State E :=
  let M := model S
  { M.updateState S with
    pairs := appendPositive M.pairs (observedTrialPair f G S (M.safeDirection S)) }

/-- The actual local Hessian norm bound gives a genuine local Lipschitz
gradient with exactly the same constant. -/
theorem gradient_lipschitzOn_of_hessian_norm (G : E → E) (H : E → E →L[ℝ] E)
    (center : E) (radius : ℝ) (M : ℝ≥0)
    (hG : ∀ z ∈ ball center radius, HasFDerivAt G (H z) z)
    (hH : ∀ z ∈ ball center radius, ‖H z‖ ≤ (M : ℝ)) :
    LipschitzOnWith M G (ball center radius) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz => (hG z hz).hasFDerivWithinAt) _ (convex_ball center radius)
  intro z hz
  exact_mod_cast hH z hz

omit [InnerProductSpace ℝ E] in
/-- Primitive local criticality and true Lipschitz control give the actual
gradient O(distance) estimate used by the safeguard localization. -/
theorem local_gradient_norm_bound (G : E → E) (center : E) (radius : ℝ)
    (hradius : 0 < radius) (M : ℝ≥0) (hG : LipschitzOnWith M G (ball center radius))
    (hzero : G center = 0) (x : E) (hx : x ∈ ball center radius) :
    ‖G x‖ ≤ (M : ℝ) * ‖x - center‖ := by
  simpa only [hzero, sub_zero] using hG.norm_sub_le hx (mem_ball_self hradius)

/-- Every safeguarded trial with 0≤t≤1 stays within the derived O(e)
radius, independently of model selection and window conditioning. -/
theorem safeguarded_trial_distance (center x g u : E) (c₁ c₂ M t : ℝ)
    (_hM : 0 ≤ M) (hc₂ : 0 ≤ c₂) (hgrad : ‖g‖ ≤ M * ‖x - center‖)
    (hu : GradientRelated c₁ c₂ g u) (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    ‖x + t • u - center‖ ≤ (1 + c₂ * M) * ‖x - center‖ := by
  have hlen : t * ‖u‖ ≤ c₂ * M * ‖x - center‖ := by
    have h₁ := mul_le_mul_of_nonneg_right ht₁ (norm_nonneg u)
    have h₂ := mul_le_mul_of_nonneg_left hgrad hc₂
    nlinarith [hu.2]
  have he : x + t • u - center = (x - center) + t • u := by abel
  rw [he]
  have hn := norm_add_le (x - center) (t • u)
  rw [norm_smul, Real.norm_of_nonneg ht] at hn
  nlinarith

/-- The actual first stored-or-accepted unit query is localized from
primitive local gradient data, without any query-bound hypothesis. -/
theorem first_probe_distance (model : State E → ModelResult E) (S : State E)
    (center : E) (M : ℝ) (hM : 0 ≤ M)
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant)
    (hgrad : ‖S.gradient‖ ≤ M * ‖S.point - center‖) :
    ‖S.point + (model S).safeDirection S - center‖ ≤
      (1 + S.normConstant * M) * ‖S.point - center‖ := by
  simpa only [one_smul] using safeguarded_trial_distance center S.point S.gradient
    ((model S).safeDirection S) _ _ M 1 hM (hc₁.trans_le hc₂).le hgrad
    (safeguard_gradientRelated _ _ _ hc₁ hc₂ _ _) (by norm_num) le_rfl

/-- Every actual reset/backtracking query after the real rejected probe
has the same O(e) radius; all generated t_j are proved to lie in (0,1]. -/
theorem reset_backtracking_distance (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (S : State E) (j : ℕ)
    (center : E) (M : ℝ) (hM : 0 ≤ M)
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant)
    (hgrad : ‖S.gradient‖ ≤ M * ‖S.point - center‖) :
    let S₁ := firstProbeState model f G S
    let u := (model S₁).safeDirection S₁
    ‖S.point + backtrackingSteps f S.point S.gradient u j • u - center‖ ≤
      (1 + S.normConstant * M) * ‖S.point - center‖ := by
  dsimp only
  let S₁ := firstProbeState model f G S
  let u := (model S₁).safeDirection S₁
  have hu : GradientRelated S.descentConstant S.normConstant S.gradient u :=
    safeguard_gradientRelated _ _ _ hc₁ hc₂ _ _
  have ht := backtrackingSteps_bounds f S.point S.gradient u j
  exact safeguarded_trial_distance center S.point S.gradient u _ _ M _ hM
    (hc₁.trans_le hc₂).le hgrad hu ht.1.le
    (ht.2.trans (pow_le_one₀ (by norm_num) (by norm_num)))

/-- The actual returned accepted length never exceeds the reset unit
trial, independently of acceptance or model regularity. -/
theorem outerSearch_length_le_one (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E) :
    (outerSearch model f G sigma S).length ≤ 1 := by
  classical
  unfold outerSearch
  dsimp only
  split
  · exact le_rfl
  · exact (backtrackingSteps_bounds _ _ _ _ _).2.trans
      (pow_le_one₀ (by norm_num) (by norm_num))

end
end krylov.XR
