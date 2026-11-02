import krylov.Functions.LocalSearchBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Order.Compact

/-!
Article: main_krylov, apG:E, the genuine local exact line search.
Use: construct the unique chord minimizer of the actual objective and prove
interior stationarity and the printed enclosure bounds from primitive local
derivative hypotheses. Existence is proved on a compact scalar chord even in
an infinite dimensional Hilbert space.
Source: the strict-convexity argument in Appendix G; mathlib's compact minimum,
derivative mean value theorem and Fermat theorem.
-/

/-!
Article: krylov, Lemma E.2 [apG:E].

The actual unique chord minimizer exists and is interior, stationary and within all printed
radius/step bounds.
Zero directions are included; nonzero-direction compactness is proved in the scalar chord
parameter. Canonical centering identifies x*=0 and H*=I.
-/

namespace krylov.Functions
noncomputable section
open Set Metric
open scoped InnerProductSpace NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Parameters of the actual closed-ball chord through a point in a direction.
Article: main_krylov, apG:E. -/
def chordParameters (x d : E) (r : ℝ) : Set ℝ :=
  {t | x + t • d ∈ closedBall (0 : E) r}

/-- A ball cuts any affine line in a convex parameter set.
Article: main_krylov, apG:E. Proof: take the affine preimage of the convex ball. -/
theorem convex_chordParameters (x d : E) (r : ℝ) :
    Convex ℝ (chordParameters x d r) := by
  intro a ha b hb u v hu hv huv
  have h := (convex_closedBall (0 : E) r) ha hb hu hv huv
  have he : x + (u * a + v * b) • d = u • (x + a • d) + v • (x + b • d) := by
    calc
      _ = (u + v) • x + (u * a + v * b) • d := by rw [huv, one_smul]
      _ = _ := by module
  change x + (u * a + v * b) • d ∈ closedBall (0 : E) r
  rw [he]
  exact h

/-- Every nonconstant chord has compact parameter set.
Article: main_krylov, apG:E.
Proof: continuity gives closedness; the reverse triangle inequality bounds the
parameter by the radius plus the starting norm divided by the direction norm. -/
theorem isCompact_chordParameters (x d : E) (r : ℝ) (hd : d ≠ 0) :
    IsCompact (chordParameters x d r) := by
  apply isCompact_of_isClosed_isBounded
  · exact isClosed_closedBall.preimage (by fun_prop)
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(r + ‖x‖) / ‖d‖, ?_⟩
    intro t ht
    have ht' : ‖x + t • d‖ ≤ r := by
      simpa only [chordParameters, mem_ofPred_eq, mem_closedBall, dist_zero_right] using ht
    apply (le_div_iff₀ (norm_pos_iff.mpr hd)).mpr
    calc
      ‖t‖ * ‖d‖ = ‖(x + t • d) - x‖ := by rw [add_sub_cancel_left, norm_smul]
      _ ≤ ‖x + t • d‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ r + ‖x‖ := add_le_add ht' le_rfl

/-- The genuine local Hessian is uniformly positive on the search ball.
Article: main_krylov, apG:E.
Proof: compare the actual Hessian to its identity value at zero in operator norm. -/
theorem local_hessian_lower (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 ≤ r)
    (hH₀ : H 0 = ContinuousLinearMap.id ℝ E) {L : ℝ≥0}
    (hLr : (L : ℝ) * r ≤ 1 / 2) (hH : LipschitzOnWith L H (closedBall 0 r))
    (z : E) (hz : z ∈ closedBall (0 : E) r) (d : E) :
    ‖d‖ ^ 2 / 2 ≤ inner ℝ (H z d) d := by
  have hn := hH.norm_sub_le hz (mem_closedBall_self hr)
  rw [hH₀, sub_zero] at hn
  have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hc : ‖H z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 :=
    hn.trans ((mul_le_mul_of_nonneg_left hz' L.coe_nonneg).trans hLr)
  have hi := abs_real_inner_le_norm ((H z - ContinuousLinearMap.id ℝ E) d) d
  have hb := (H z - ContinuousLinearMap.id ℝ E).le_opNorm d
  have hnorm : ‖(H z - ContinuousLinearMap.id ℝ E) d‖ ≤ ‖d‖ / 2 := by
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg d)])
  have hi' := hi.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg d))
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_left,
    real_inner_self_eq_norm_sq] at hi'
  have := (abs_le.mp hi').1
  nlinarith

/-- A nonconstant actual chord restriction is strictly convex on its closed chord.
Article: main_krylov, apG:E.
Proof: the genuine second scalar derivative is the positive Hessian quadratic
form; strict monotonicity of the first derivative gives strict convexity. -/
theorem strictConvexOn_chord (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 ≤ r) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x d : E) (hd : d ≠ 0) :
    StrictConvexOn ℝ (chordParameters x d r) (fun t : ℝ => f (x + t • d)) := by
  let q := fun t : ℝ => f (x + t • d)
  let q₁ := fun t : ℝ => inner ℝ (G (x + t • d)) d
  have hq t (ht : t ∈ chordParameters x d r) : HasDerivAt q (q₁ t) t := by
    exact segment_hasDerivAt f (fun z => innerSL ℝ (G z)) x d t (hF _ ht)
  have hq₁ t (ht : t ∈ chordParameters x d r) :
      HasDerivAt q₁ (inner ℝ (H (x + t • d) d) d) t := by
    simpa using (segment_hasDerivAt G H x d t (hG _ ht)).inner ℝ (hasDerivAt_const t d)
  have hmono : StrictMonoOn q₁ (chordParameters x d r) := by
    apply strictMonoOn_of_deriv_pos (convex_chordParameters x d r)
      (fun t ht => (hq₁ t ht).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hq₁ t (interior_subset ht)).deriv]
    have ht' : t ∈ chordParameters x d r := interior_subset ht
    have hb := local_hessian_lower H hr hH₀ hLr hH (x + t • d) ht' d
    have hp : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
    linarith
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_chordParameters x d r)
    (fun t ht => (hq t ht).continuousAt.continuousWithinAt)
  intro a ha b hb hab
  rw [(hq a (interior_subset ha)).deriv, (hq b (interior_subset hb)).deriv]
  exact hmono (interior_subset ha) (interior_subset hb) hab

/-- A minimum of the genuine objective on the entire local closed-ball chord.
Article: main_krylov, apG:E. No search result or derivative conclusion is stored. -/
def IsChordMinimum (f : E → ℝ) (x d : E) (r : ℝ) (y : E) : Prop :=
  y ∈ closedBall (0 : E) r ∧ (∃ t : ℝ, y = x + t • d) ∧
    ∀ t ∈ chordParameters x d r, f y ≤ f (x + t • d)

/-- The actual local chord has exactly one minimizing point, including zero directions.
Article: main_krylov, apG:E.
Proof: a nonconstant chord is compact in its scalar parameter and its genuine
restriction is strictly convex. A zero direction gives the singleton chord. -/
theorem existsUnique_local_chord_minimum (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hH₀ : H 0 = ContinuousLinearMap.id ℝ E) {L : ℝ≥0}
    (hLr : (L : ℝ) * r ≤ 1 / 2) (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x d : E) (hx : x ∈ closedBall (0 : E) r) :
    ∃! y : E, IsChordMinimum f x d r y := by
  by_cases hd : d = 0
  · refine ⟨x, ⟨hx, ⟨0, by simp⟩, ?_⟩, ?_⟩
    · intro t _
      simp [hd]
    · intro y hy
      obtain ⟨t, ht⟩ := hy.2.1
      simpa [hd] using ht
  · have hne : (chordParameters x d r).Nonempty := ⟨0, by simpa [chordParameters] using hx⟩
    have hc : ContinuousOn (fun t : ℝ => f (x + t • d)) (chordParameters x d r) := by
      intro t ht
      exact (segment_hasDerivAt f (fun z => innerSL ℝ (G z)) x d t
        (hF _ ht)).continuousAt.continuousWithinAt
    obtain ⟨t, ht, hmin⟩ := (isCompact_chordParameters x d r hd).exists_isMinOn hne hc
    refine ⟨x + t • d, ⟨ht, ⟨t, rfl⟩, hmin⟩, ?_⟩
    intro y hy
    obtain ⟨s, rfl⟩ := hy.2.1
    have hs : s ∈ chordParameters x d r := hy.1
    have hsmin : IsMinOn (fun t : ℝ => f (x + t • d)) (chordParameters x d r) s := hy.2.2
    have he := (strictConvexOn_chord f G H hr.le hH₀ hLr hH hF hG x d hd).eq_of_isMinOn
      hsmin hmin hs ht
    rw [he]

variable [CompleteSpace E]

/-- The actual unique minimizer is interior, stationary and satisfies all printed bounds.
Article: main_krylov, apG:E.
Proof: compare its actual value with the admitted initial point, apply the
proved cubic sublevel enclosure, and use Fermat's theorem on the now interior
scalar chord restriction. -/
theorem local_chord_minimum_spec (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x d y : E) (hx : ‖x‖ < r / 2) (hy : IsChordMinimum f x d r y) :
    ‖y‖ ≤ min (Real.sqrt 3) (1 + 2 * (L : ℝ) * ‖x‖) * ‖x‖ ∧
      y ∈ ball (0 : E) r ∧ inner ℝ (G y) d = 0 ∧ ‖y - x‖ ≤ 3 * ‖x‖ := by
  have hx' : x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg x]
  have hv : f y ≤ f x := by
    simpa using hy.2.2 0 (by simpa [chordParameters] using hx')
  obtain ⟨hrough, hsharp, hinter, hstep⟩ := local_sublevel_search_bounds f G H hr
    hG₀ hH₀ hLr hH hF hG x y hx hy.1 hv
  refine ⟨?_, hinter, ?_, hstep⟩
  · rw [min_mul_of_nonneg _ _ (norm_nonneg x)]
    exact le_min hrough hsharp
  · obtain ⟨t, ht⟩ := hy.2.1
    have hK : chordParameters x d r ∈ 𝓝 t := by
      have hn : (fun s : ℝ => x + s • d) ⁻¹' ball (0 : E) r ∈ 𝓝 t :=
        (by fun_prop : Continuous (fun s : ℝ => x + s • d)).continuousAt.preimage_mem_nhds
          (isOpen_ball.mem_nhds (by simpa [← ht] using hinter))
      exact Filter.mem_of_superset hn (fun _ hs => ball_subset_closedBall hs)
    have hmin : IsMinOn (fun s : ℝ => f (x + s • d)) (chordParameters x d r) t := by
      intro s hs
      change f (x + t • d) ≤ f (x + s • d)
      rw [← ht]
      exact hy.2.2 s hs
    have hd := segment_hasDerivAt f (fun z => innerSL ℝ (G z)) x d t
      (hF _ (by simpa [← ht] using hy.1))
    have hz := (hmin.isLocalMin hK).deriv_eq_zero
    rw [hd.deriv] at hz
    simpa [← ht] using hz

/-- The article's exact search exists uniquely for the mathematical Riesz gradient.
Article: main_krylov, apG:E, existence, uniqueness, bounds and stationarity.
Proof: differentiability identifies the scalar derivative with the genuine
gradient. Apply the constructed chord minimum and its proved local enclosure. -/
theorem exact_gradient_search (f : E → ℝ) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hf : ∀ z ∈ closedBall (0 : E) r, DifferentiableAt ℝ f z)
    (hg₀ : gradient f (0 : E) = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt (gradient f) (H z) z)
    (x d : E) (hx : ‖x‖ < r / 2) :
    (∃! y : E, IsChordMinimum f x d r y) ∧
      ∀ y : E, IsChordMinimum f x d r y →
        ‖y‖ ≤ min (Real.sqrt 3) (1 + 2 * (L : ℝ) * ‖x‖) * ‖x‖ ∧
          y ∈ ball (0 : E) r ∧ inner ℝ (gradient f y) d = 0 ∧
            ‖y - x‖ ≤ 3 * ‖x‖ := by
  have hF z (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    (hf z hz).hasGradientAt.hasFDerivAt
  have hx' : x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg x]
  refine ⟨existsUnique_local_chord_minimum f (gradient f) H hr hH₀ hLr hH hF hG x d hx', ?_⟩
  exact fun y hy => local_chord_minimum_spec f (gradient f) H hr hg₀ hH₀ hLr hH hF hG x d y hx hy

end
end krylov.Functions
