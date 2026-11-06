import nesterov.Flow.Model
import polyak.Interpolation.Minimum
import polyak.Functions.Transforms

/-!
Article: §3, existence and uniqueness of the minimizer in F_m.
Use: a direct strongly convex epigraph argument works on arbitrary Hilbert
spaces without a finite global gradient Lipschitz constant.  It reuses the
proved Cauchy minimization construction from Polyak's interpolation package.
-/

noncomputable section

namespace nesterov.Flow

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem StronglyConvexObjective.midpoint_bound {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) (x y : E) :
    f ((1 / 2 : ℝ) • (x + y)) + m / 8 * ‖x - y‖ ^ 2 ≤ (f x + f y) / 2 := by
  let z := (1 / 2 : ℝ) • (x + y)
  have hx := hf.tangent_lower z x
  have hy := hf.tangent_lower z y
  have h1 : x - z = (1 / 2 : ℝ) • (x - y) := by dsimp [z]; module
  have h2 : y - z = -((1 / 2 : ℝ) • (x - y)) := by dsimp [z]; module
  rw [h1] at hx
  rw [h2] at hy
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    inner_neg_right, inner_smul_right] at hx hy
  change f z + _ ≤ _
  nlinarith

theorem StronglyConvexObjective.bddBelow_range {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) : BddBelow (Set.range f) := by
  let N := ‖gradient f 0‖
  refine ⟨f 0 - N ^ 2 / (2 * m), ?_⟩
  rintro _ ⟨x, rfl⟩
  have hh := hf.tangent_lower 0 x
  simp only [sub_zero] at hh
  have hi := real_inner_le_norm (-gradient f 0) x
  simp only [inner_neg_left, norm_neg] at hi
  have hbase : f 0 - N * ‖x‖ + m / 2 * ‖x‖ ^ 2 ≤ f x := by dsimp [N]; linarith
  have hm : 0 < 2 * m := by linarith [hf.m_pos]
  have hmul := mul_le_mul_of_nonneg_left hbase hm.le
  have he : N ^ 2 / (2 * m) * (2 * m) = N ^ 2 := by field_simp [ne_of_gt hf.m_pos]
  have hs := sq_nonneg (m * ‖x‖ - N)
  apply (mul_le_mul_iff_of_pos_right hm).mp
  nlinarith

/-- Every objective in the uncentered F_m class has a genuine unique minimum. -/
theorem StronglyConvexObjective.existsUnique_minimizer {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) : ∃! a : E, ∀ y : E, f a ≤ f y := by
  let S : Set (E × ℝ) := {p | f p.1 ≤ p.2}
  have hne : S.Nonempty := ⟨(0, f 0), by change f 0 ≤ f 0; exact le_rfl⟩
  have hclosed : IsClosed S := isClosed_le (hf.differentiable.continuous.comp continuous_fst) continuous_snd
  have hbounded : BddBelow (Prod.snd '' S) := by
    obtain ⟨B, hB⟩ := hf.bddBelow_range
    refine ⟨B, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (hB ⟨p.1, rfl⟩).trans hp
  have hmid : ∀ p ∈ S, ∀ q ∈ S,
      (((1 / 2 : ℝ) • (p.1 + q.1)), (p.2 + q.2) / 2 - (m / 8) * ‖p.1 - q.1‖ ^ 2) ∈ S := by
    intro p hp q hq
    have hh := hf.midpoint_bound p.1 q.1
    change f _ ≤ _
    change f p.1 ≤ p.2 at hp
    change f q.1 ≤ q.2 at hq
    linarith
  obtain ⟨p, hp, hpmin⟩ := polyak.Interpolation.exists_min_height hne hclosed hbounded
    (show 0 < m / 8 by linarith [hf.m_pos]) hmid
  have hmin (y : E) : f p.1 ≤ f y :=
    hp.trans (hpmin (y, f y) (by change f y ≤ f y; exact le_rfl))
  refine ⟨p.1, hmin, ?_⟩
  intro y hy
  have hh := hf.midpoint_bound y p.1
  have hl := hmin ((1 / 2 : ℝ) • (y + p.1))
  have he : f y = f p.1 := le_antisymm (hy p.1) (hmin y)
  rw [he] at hh
  have hz : ‖y - p.1‖ = 0 := by
    by_contra hn
    have hp := mul_pos (show 0 < m / 8 by linarith [hf.m_pos])
      (sq_pos_of_pos ((norm_nonneg (y - p.1)).lt_of_ne' hn))
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem StronglyConvexObjective.gradient_zero_at_minimizer {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) {a : E} (ha : ∀ y, f a ≤ f y) : gradient f a = 0 := by
  have hmin : IsLocalMin f a := Filter.Eventually.of_forall ha
  have hz := hmin.hasFDerivAt_eq_zero (hf.differentiable a).hasFDerivAt
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa only [map_zero, toDual_gradient] using hz

theorem StronglyConvexObjective.center {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) (a : E) :
    StronglyConvexObjective m (polyak.centerObjective f a) := by
  have hg := polyak.hasGradientAt_centerObjective hf.differentiable a
  refine ⟨hf.m_pos, fun x => (hg x).differentiableAt, ?_, ?_⟩
  · intro x y
    rw [(hg x).gradient]
    have hh := hf.tangent_lower (a + x) (a + y)
    dsimp [polyak.centerObjective]
    simp only [add_sub_add_left_eq_sub] at hh
    linarith
  · intro R
    obtain ⟨K, hK⟩ := hf.gradient_lipschitz_bounded (‖a‖ + R)
    refine ⟨K, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hx' : a + x ∈ Metric.closedBall (0 : E) (‖a‖ + R) := by
      rw [mem_closedBall_zero_iff] at hx ⊢
      exact (norm_add_le _ _).trans (by linarith)
    have hy' : a + y ∈ Metric.closedBall (0 : E) (‖a‖ + R) := by
      rw [mem_closedBall_zero_iff] at hy ⊢
      exact (norm_add_le _ _).trans (by linarith)
    rw [(hg x).gradient, (hg y).gradient]
    simpa using hK.dist_le_mul (a + x) hx' (a + y) hy'

/-- The normalization used in §3 loses no member of the uncentered class. -/
theorem StronglyConvexObjective.exists_centered {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) :
    ∃ a : E, (∀ y : E, f a ≤ f y) ∧ Objective m (polyak.centerObjective f a) := by
  obtain ⟨a, ha, _⟩ := hf.existsUnique_minimizer
  refine ⟨a, ha, hf.center a, ?_, ?_⟩
  · simp [polyak.centerObjective]
  · rw [(polyak.hasGradientAt_centerObjective hf.differentiable a 0).gradient]
    simpa using hf.gradient_zero_at_minimizer ha

end nesterov.Flow
