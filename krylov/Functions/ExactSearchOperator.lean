import krylov.Functions.ExactSearchComparison
import krylov.Functions.SegmentHessian
import krylov.Reference.CG

/-!
Article: main_krylov, lem:cycle-transfer, genuine search/operator dictionary.
Use: identify the actual nonlinear chord minimizer with the existing
data-only exact-search quotient for its true averaged Hessian. This closes
the search primitive needed to compare native function and operator runs.
Source: Appendix G; the genuine segment FTC and actual search stationarity.
-/

namespace krylov.Functions
noncomputable section
open Set Metric chebyshev1.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Actual local segment averages remain within one-half of the identity.
Article: main_krylov, lem:cycle-transfer, positive actual search curvature.
Proof: integrate the sharp endpoint Lipschitz comparison on the original enclosed segment. -/
theorem averagedHessian_local_identity_bound (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 ≤ r) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (a b : E) (ha : a ∈ closedBall (0 : E) r) (hb : b ∈ closedBall (0 : E) r) :
    ‖averagedDerivative H a (b - a) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • (b - a) ∈ closedBall (0 : E) r := by
    apply (convex_closedBall (0 : E) r).add_smul_mem ha _ ht
    simpa only [add_sub_cancel] using hb
  have hc := hH.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
  have hzero : ContinuousOn (fun t : ℝ => H ((0 : E) + t • (0 : E))) (Icc 0 1) := by
    simpa only [smul_zero, add_zero] using (continuousOn_const : ContinuousOn (fun _ : ℝ => H 0) (Icc 0 1))
  have hz : (0 : E) ∈ closedBall (0 : E) r := mem_closedBall_self hr
  have hcomp := averagedHessian_endpoint_bound H a (b - a) 0 0 (L : ℝ) hc hzero L.coe_nonneg
    (fun t ht => by simpa only [smul_zero, add_zero] using hH.norm_sub_le (hseg t ht) hz)
  have he : averagedDerivative H 0 0 = H 0 := by simp [averagedDerivative]
  rw [he, hH₀] at hcomp
  simp only [sub_zero, add_sub_cancel, add_zero] at hcomp
  have ha' : ‖a‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using ha
  have hb' : ‖b‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hb
  exact hcomp.trans (by nlinarith [L.coe_nonneg])

omit [CompleteSpace E] in
/-- The one-half identity neighborhood has genuinely positive curvature in every nonzero direction.
Article: main_krylov, lem:cycle-transfer, denominator nonvanishing for actual search. -/
theorem inner_lower_of_identity_bound (A : E →L[ℝ] E)
    (hA : ‖A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (d : E) :
    ‖d‖ ^ 2 / 2 ≤ inner ℝ d (A d) := by
  have hi := abs_real_inner_le_norm d ((A - ContinuousLinearMap.id ℝ E) d)
  have hb := (A - ContinuousLinearMap.id ℝ E).le_opNorm d
  have hn : ‖(A - ContinuousLinearMap.id ℝ E) d‖ ≤ ‖d‖ / 2 := by
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hA (norm_nonneg d)])
  have hi' := hi.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg d))
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_right,
    real_inner_self_eq_norm_sq] at hi'
  have := (abs_le.mp hi').1
  nlinarith

/-- The actual nonlinear exact search executes the operator quotient for its true segment average.
Article: main_krylov, lem:cycle-transfer, the actual native search/operator bridge.
Proof: the genuine FTC gives the observed gradient increment. The actual
stationarity equation and positive averaged curvature determine its unique
search quotient, including the true zero-direction case. -/
theorem local_chord_operator_search (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x d y : E) (hx : ‖x‖ < r / 2) (hy : IsChordMinimum f x d r y) :
    let A := averagedDerivative H x (y - x)
    y - x = lineLength (G x) d (A d) • d ∧ G y = searchedGradient (G x) d (A d) := by
  dsimp only
  let A := averagedDerivative H x (y - x)
  have hx' : x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg x]
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ closedBall (0 : E) r := by
    apply (convex_closedBall (0 : E) r).add_smul_mem hx' _ ht
    simpa only [add_sub_cancel] using hy.1
  have hc := hH.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
  have hFTC := averagedDerivative_apply G H x (y - x) hc (fun t ht => hG _ (hseg t ht))
  simp only [add_sub_cancel] at hFTC
  change A (y - x) = G y - G x at hFTC
  have hstat := (local_chord_minimum_spec f G H hr hG₀ hH₀ hLr hH hF hG x d y hx hy).2.2.1
  by_cases hd : d = 0
  · obtain ⟨t, ht⟩ := hy.2.1
    have he : y = x := by simpa only [hd, smul_zero, add_zero] using ht
    simp [hd, he, lineLength, searchedGradient]
  obtain ⟨t, ht⟩ := hy.2.1
  have hs : y - x = t • d := by rw [ht]; module
  have hpos : 0 < inner ℝ d (A d) := by
    have hbound := averagedHessian_local_identity_bound H hr.le hH₀ hLr hH x y hx' hy.1
    have hlo := inner_lower_of_identity_bound A hbound d
    exact (by positivity : 0 < ‖d‖ ^ 2 / 2).trans_le hlo
  have hgrad : G y = G x + t • A d := by
    rw [hs, map_smul] at hFTC
    exact (eq_add_of_sub_eq hFTC.symm).trans (add_comm _ _)
  have hp : inner ℝ d (G x) + t * inner ℝ d (A d) = 0 := by
    rw [real_inner_comm, hgrad, inner_add_right, real_inner_smul_right] at hstat
    exact hstat
  have hlength : lineLength (G x) d (A d) = t := by
    rw [lineLength]
    apply (div_eq_iff hpos.ne').mpr
    linarith only [hp]
  refine ⟨?_, ?_⟩
  · change y - x = lineLength (G x) d (A d) • d
    rw [hlength]
    exact hs
  · change G y = G x + lineLength (G x) d (A d) • A d
    rw [hlength]
    exact hgrad

end
end krylov.Functions
