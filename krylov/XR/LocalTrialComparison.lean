import krylov.Stability.CompactSmooth
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Article: main_krylov, lem:xr-local, the mixed-derivative trial comparison.
Use: a genuine C² joint output with locally constant quadratic-reference
slice has a trial sensitivity proportional to the actual operator error.
Multiplying by a first-order trial change yields the printed second-order
comparison. Trial policies themselves need only the stated pointwise
first-order difference bound in this estimate.
Source: local Lipschitz continuity of the true first derivative and the
convex derivative mean-value theorem, with the reference derivative proved zero.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology Asymptotics
variable {X T F : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup T] [NormedSpace ℝ T]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Genuine C² regularity and quadratic trial-independence give a mixed
operator-error/trial-difference bound, without postulating a zero mixed jet. -/
theorem c2_reference_trial_difference (f : X × T → F) (t₀ : T)
    (hf : ContDiffAt ℝ 2 f (0, t₀))
    (hzero : ∀ᶠ t in 𝓝 t₀, f (0, t) = f (0, t₀)) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 ≤ C ∧ ∀ e : X, ‖e‖ < delta →
      ∀ t₁ t₂ : T, ‖t₁ - t₀‖ < delta → ‖t₂ - t₀‖ < delta →
        ‖f (e, t₂) - f (e, t₁)‖ ≤ C * ‖e‖ * ‖t₂ - t₁‖ := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) (0, t₀) := hf.fderiv_right (by norm_num)
  obtain ⟨L, U, hU, hLip⟩ := hdf.exists_lipschitzOnWith
  have hdata : ∀ᶠ z in 𝓝 (0, t₀), DifferentiableAt ℝ f z ∧ z ∈ U := by
    filter_upwards [hf.eventually (by norm_num), hU] with z hz hu
    exact ⟨hz.differentiableAt (by norm_num), hu⟩
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp hdata
  obtain ⟨r₀, hr₀, hreference⟩ := Metric.eventually_nhds_iff.mp hzero
  let delta := min r r₀ / 2
  have hd : 0 < delta := by dsimp only [delta]; positivity
  have hdr : delta < r := by dsimp only [delta]; have := min_le_left r r₀; linarith
  have hd₀ : delta < r₀ := by dsimp only [delta]; have := min_le_right r r₀; linarith
  refine ⟨delta, L, hd, L.coe_nonneg, ?_⟩
  intro e he
  have hpoint (t : T) (ht : t ∈ ball t₀ delta) : dist (e, t) (0, t₀) < r := by
    rw [Prod.dist_eq, dist_zero_right]
    exact max_lt (he.trans hdr) ((show dist t t₀ < delta from ht).trans hdr)
  have hbase (t : T) (ht : t ∈ ball t₀ delta) : dist ((0 : X), t) (0, t₀) < r := by
    rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
    exact (show dist t t₀ < delta from ht).trans hdr
  have hzeroD (t : T) (ht : t ∈ ball t₀ delta) :
      (fderiv ℝ f (0, t)).comp (ContinuousLinearMap.inr ℝ X T) = 0 := by
    have hdiff := (hlocal (hbase t ht)).1
    have hin : HasFDerivAt (fun v : T => ((0 : X), v)) (ContinuousLinearMap.inr ℝ X T) t :=
      (ContinuousLinearMap.inr ℝ X T).hasFDerivAt
    have hder := hdiff.hasFDerivAt.comp t hin
    have ht₀ : t ∈ ball t₀ r₀ := (show dist t t₀ < delta from ht).trans hd₀
    have hmem : ∀ᶠ v in 𝓝 t, v ∈ ball t₀ r₀ := isOpen_ball.mem_nhds ht₀
    have heq : (fun v : T => f (0, v)) =ᶠ[𝓝 t] fun _ => f (0, t₀) :=
      hmem.mono (fun _ hv => hreference hv)
    exact hder.unique ((hasFDerivAt_const (f (0, t₀)) t).congr_of_eventuallyEq heq)
  have hder (t : T) (ht : t ∈ ball t₀ delta) :
      HasFDerivAt (fun v : T => f (e, v))
        ((fderiv ℝ f (e, t)).comp (ContinuousLinearMap.inr ℝ X T)) t := by
    have hin : HasFDerivAt (fun v : T => (e, v)) (ContinuousLinearMap.inr ℝ X T) t := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add, ContinuousLinearMap.inr_apply] using
        ((ContinuousLinearMap.inr ℝ X T).hasFDerivAt (x := t)).const_add (e, 0)
    exact (hlocal (hpoint t ht)).1.hasFDerivAt.comp t hin
  have hbound (t : T) (ht : t ∈ ball t₀ delta) :
      ‖(fderiv ℝ f (e, t)).comp (ContinuousLinearMap.inr ℝ X T)‖ ≤ (L : ℝ) * ‖e‖ := by
    have hL := hLip.norm_sub_le (hlocal (hpoint t ht)).2 (hlocal (hbase t ht)).2
    rw [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg e)] at hL
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg L.coe_nonneg (norm_nonneg e))
    intro v
    have hz : fderiv ℝ f (0, t) (0, v) = 0 := by
      have hh := congrArg (fun D : T →L[ℝ] F => D v) (hzeroD t ht)
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, _root_.zero_apply] using hh
    have heq : ((fderiv ℝ f (e, t)).comp (ContinuousLinearMap.inr ℝ X T)) v =
        (fderiv ℝ f (e, t) - fderiv ℝ f (0, t)) (0, v) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, sub_apply, hz, sub_zero]
    rw [heq]
    exact ((fderiv ℝ f (e, t) - fderiv ℝ f (0, t)).le_opNorm (0, v)).trans (by
      rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg v)]
      exact mul_le_mul_of_nonneg_right hL (norm_nonneg v))
  intro t₁ t₂ ht₁ ht₂
  exact (convex_ball t₀ delta).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun t ht => (hder t ht).hasFDerivWithinAt) hbound
    (by simpa only [mem_ball, dist_eq_norm] using ht₁)
    (by simpa only [mem_ball, dist_eq_norm] using ht₂)

/-- The source's first-order trial difference gives the genuine quadratic
operator-sequence output comparison, even without differentiating either
trial policy. The joint C² output and its true reference constancy suffice. -/
theorem c2_reference_trial_comparison_bigO (f : X × T → F) (t₀ : T)
    (hf : ContDiffAt ℝ 2 f (0, t₀))
    (hzero : ∀ᶠ t in 𝓝 t₀, f (0, t) = f (0, t₀))
    (t₁ t₂ : X → T) (ht₁ : Tendsto t₁ (𝓝 0) (𝓝 t₀)) (ht₂ : Tendsto t₂ (𝓝 0) (𝓝 t₀))
    (hdiff : (fun e => t₂ e - t₁ e) =O[𝓝 0] (fun e : X => ‖e‖)) :
    (fun e => f (e, t₂ e) - f (e, t₁ e)) =O[𝓝 0] (fun e : X => ‖e‖ ^ 2) := by
  obtain ⟨delta, C, hd, hC, hbound⟩ := c2_reference_trial_difference f t₀ hf hzero
  obtain ⟨K, _hK, hKbound⟩ := hdiff.exists_nonneg
  have he : ∀ᶠ e in 𝓝 (0 : X), ‖e‖ < delta := by
    have hh : ∀ᶠ e in 𝓝 (0 : X), e ∈ ball 0 delta := ball_mem_nhds 0 hd
    simpa only [mem_ball, dist_zero_right] using hh
  apply IsBigO.of_bound (C * K)
  filter_upwards [he, ht₁.eventually (ball_mem_nhds t₀ hd), ht₂.eventually (ball_mem_nhds t₀ hd), hKbound.bound]
    with e he ht₁ ht₂ hdifference
  have hs : ‖t₂ e - t₁ e‖ ≤ K * ‖e‖ := by
    simpa only [Real.norm_eq_abs, abs_norm] using hdifference
  have hh := hbound e he (t₁ e) (t₂ e)
    (by simpa only [mem_ball, dist_eq_norm] using ht₁)
    (by simpa only [mem_ball, dist_eq_norm] using ht₂)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖e‖)]
  calc
    _ ≤ (C * ‖e‖) * ‖t₂ e - t₁ e‖ := hh
    _ ≤ (C * ‖e‖) * (K * ‖e‖) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hC (norm_nonneg e))
    _ = _ := by ring

end
end krylov.XR
