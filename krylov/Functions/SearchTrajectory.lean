import krylov.Functions.ExactSearchComparison

/-!
Article: main_krylov, lem:cycle-transfer, genuine finite exact-search localization.
Use: derive common query bounds from actual objective minimization, rather
than storing localization in a trajectory hypothesis. Monotonicity of the
actual values gives a bound independent of the finite number of searches.
Source: Appendix G, the proved local potential comparison and chord minimum.
-/

namespace krylov.Functions
noncomputable section
open Set Metric
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual unique chord minimizer, totalized only when the local minimum does not exist.
Article: main_krylov, apG:E and lem:cycle-transfer.
Use: a concrete local-search executor, not a prescribed response or trajectory bound. -/
def localExactPoint (f : E → ℝ) (x d : E) (r : ℝ) : E := by
  classical
  exact if h : ∃! y : E, IsChordMinimum f x d r y then Classical.choose h.exists else x

/-- When the genuine local minimum exists, the actual selected point is that minimum.
Article: main_krylov, apG:E. -/
theorem localExactPoint_spec (f : E → ℝ) (x d : E) (r : ℝ)
    (h : ∃! y : E, IsChordMinimum f x d r y) :
    IsChordMinimum f x d r (localExactPoint f x d r) := by
  rw [localExactPoint, dite_eq_left h]
  exact Classical.choose_spec h.exists

/-- The actual adaptive search history retains all its previous query points.
Article: main_krylov, lem:cycle-transfer, finite native query execution.
Use: the direction may depend on the complete genuine previous history. -/
def exactSearchHistory (f : E → ℝ) (r : ℝ) (direction : List E → E) (x₀ : E) : ℕ → List E
  | 0 => [x₀]
  | k + 1 =>
      let hist := exactSearchHistory f r direction x₀ k
      localExactPoint f (hist.headD x₀) (direction hist) r :: hist

/-- The actual query point read from the adaptive search history.
Article: main_krylov, lem:cycle-transfer. -/
def exactSearchPoint (f : E → ℝ) (r : ℝ) (direction : List E → E) (x₀ : E) (k : ℕ) : E :=
  (exactSearchHistory f r direction x₀ k).headD x₀

/-- Every step of the concrete adaptive search executor is the genuine unique local minimum.
Article: main_krylov, lem:cycle-transfer, existence before any query localization.
Proof: induction proves membership in the original local chord domain; the
constructed unique minimizer then supplies the next actual query point. -/
theorem exactSearchPoint_chord_steps (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (direction : List E → E) (x₀ : E) (hx₀ : x₀ ∈ closedBall (0 : E) r) :
    ∀ k : ℕ, IsChordMinimum f (exactSearchPoint f r direction x₀ k)
      (direction (exactSearchHistory f r direction x₀ k)) r
      (exactSearchPoint f r direction x₀ (k + 1)) := by
  have hball : ∀ k : ℕ, exactSearchPoint f r direction x₀ k ∈ closedBall (0 : E) r := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k ih =>
      have hmin := existsUnique_local_chord_minimum f G H hr hH₀ hLr hH hF hG
        (exactSearchPoint f r direction x₀ k) (direction (exactSearchHistory f r direction x₀ k)) ih
      exact (localExactPoint_spec f _ _ r hmin).1
  intro k
  have hmin := existsUnique_local_chord_minimum f G H hr hH₀ hLr hH hF hG
    (exactSearchPoint f r direction x₀ k) (direction (exactSearchHistory f r direction x₀ k)) (hball k)
  exact localExactPoint_spec f _ _ r hmin

/-- An actual finite search trajectory stays in the original starting sublevel set.
Article: main_krylov, lem:cycle-transfer, query localization before any Taylor substitution.
Proof: use the initial point as an admissible parameter in each real chord minimum. -/
theorem exact_search_trajectory_sublevel (f : E → ℝ) (x d : ℕ → E) (r : ℝ) (N : ℕ)
    (hx₀ : x 0 ∈ closedBall (0 : E) r)
    (hstep : ∀ k < N, IsChordMinimum f (x k) (d k) r (x (k + 1))) :
    ∀ k ≤ N, x k ∈ closedBall (0 : E) r ∧ f (x k) ≤ f (x 0) := by
  intro k hk
  induction k with
  | zero => exact ⟨hx₀, le_rfl⟩
  | succ k ih =>
    have hkN : k < N := by omega
    have hprev := ih (by omega)
    have hm := hstep k hkN
    have hv : f (x (k + 1)) ≤ f (x k) := by
      simpa using hm.2.2 0 (by simpa [chordParameters] using hprev.1)
    exact ⟨hm.1, hv.trans hprev.2⟩

variable [CompleteSpace E]

/-- Every actual exact-search query is localized by the initial scale, independently of cycle length.
Article: main_krylov, lem:cycle-transfer, the genuine O(e_c) query bound for search-only cycles.
Proof: all actual values stay below the first value; apply the sharp original
potential comparison once to the common initial point and each real query. -/
theorem exact_search_trajectory_localization (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x d : ℕ → E) (N : ℕ) (hx : ‖x 0‖ < r / 2)
    (hstep : ∀ k < N, IsChordMinimum f (x k) (d k) r (x (k + 1))) :
    ∀ k ≤ N, ‖x k‖ ≤ Real.sqrt 3 * ‖x 0‖ ∧
      ‖x k‖ ≤ (1 + 2 * (L : ℝ) * ‖x 0‖) * ‖x 0‖ ∧ x k ∈ ball (0 : E) r := by
  have hx₀ : x 0 ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg (x 0)]
  intro k hk
  have hsub := exact_search_trajectory_sublevel f x d r N hx₀ hstep k hk
  have hb := local_sublevel_search_bounds f G H hr hG₀ hH₀ hLr hH hF hG
    (x 0) (x k) hx hsub.1 hsub.2
  exact ⟨hb.1, hb.2.1, by simpa only [mem_ball, dist_zero_right] using hb.2.2.1⟩

/-- One common initial neighborhood gives actual stationarity and quadratic search error at every node.
Article: main_krylov, lem:cycle-transfer, uniform finite exact-search primitives.
Proof: derive the needed input neighborhoods from the common actual sublevel
bound, then apply the genuine local-search and quadratic-comparison theorems. -/
theorem exact_search_trajectory_comparison (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x d : ℕ → E) (N : ℕ) (hx : ‖x 0‖ < r / 4)
    (hstep : ∀ k < N, IsChordMinimum f (x k) (d k) r (x (k + 1))) :
    ∀ k < N, inner ℝ (G (x (k + 1))) (d k) = 0 ∧
      ‖x (k + 1) - quadraticSearchPoint (x k) (d k)‖ ≤
        9 * (L : ℝ) / 2 * ‖x 0‖ ^ 2 := by
  have hx' : ‖x 0‖ < r / 2 := by linarith
  have hloc := exact_search_trajectory_localization f G H hr hG₀ hH₀ hLr hH hF hG x d N hx' hstep
  intro k hk
  have hn := (hloc k hk.le).1
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt0 := Real.sqrt_nonneg (3 : ℝ)
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith
  have hinput : ‖x k‖ < r / 2 := by
    have htwo := mul_le_mul_of_nonneg_right hsqrt2 (norm_nonneg (x 0))
    linarith
  have hspec := local_chord_minimum_spec f G H hr hG₀ hH₀ hLr hH hF hG
    (x k) (d k) (x (k + 1)) hinput (hstep k hk)
  refine ⟨hspec.2.2.1, ?_⟩
  have hcomp := local_exact_search_quadratic_error f G H hr hG₀ hH₀ hLr hH hF hG
    (x k) (d k) (x (k + 1)) hinput (hstep k hk)
  have hsq : ‖x k‖ ^ 2 ≤ 3 * ‖x 0‖ ^ 2 := by
    have hb := (sq_le_sq₀ (norm_nonneg (x k))
      (mul_nonneg hsqrt0 (norm_nonneg (x 0)))).mpr hn
    rw [mul_pow, hsqrt] at hb
    exact hb
  exact hcomp.trans (by nlinarith [L.coe_nonneg])

/-- The concrete adaptive executor has uniformly localized genuine query points for every history rule.
Article: main_krylov, lem:cycle-transfer, the search-only query-localization primitive.
Proof: existence and validity of every actual chord step were proved from the
original derivatives; objective monotonicity supplies the common shrinking bound. -/
theorem exactSearchPoint_localization (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (direction : List E → E) (x₀ : E) (hx₀ : ‖x₀‖ < r / 2) :
    ∀ k : ℕ, ‖exactSearchPoint f r direction x₀ k‖ ≤ Real.sqrt 3 * ‖x₀‖ ∧
      ‖exactSearchPoint f r direction x₀ k‖ ≤ (1 + 2 * (L : ℝ) * ‖x₀‖) * ‖x₀‖ ∧
      exactSearchPoint f r direction x₀ k ∈ ball (0 : E) r := by
  have hx₀' : x₀ ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg x₀]
  have hsteps := exactSearchPoint_chord_steps f G H hr hH₀ hLr hH hF hG direction x₀ hx₀'
  intro k
  exact exact_search_trajectory_localization f G H hr hG₀ hH₀ hLr hH hF hG
    (exactSearchPoint f r direction x₀) (fun j => direction (exactSearchHistory f r direction x₀ j))
    k hx₀ (fun j _ => hsteps j) k le_rfl

end
end krylov.Functions
