import krylov.XR.LocalBacktracking
import krylov.XR.ExecutionDescent

/-!
Article: main_krylov, thm:grow, local accepted-step lower bound.
Use: establish a uniform actual Armijo step on a tail lying near its
accepted limit, using only f/G on one local ball. The single rejected
probe and reset are included; no global gradient regularity is needed.
Source: the genuine local descent lemma and actual clipped backtracking.
-/

namespace krylov.XR
noncomputable section
open Set Metric
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sufficient local trial length, retaining both the local-ball and the
genuine descent restrictions. -/
def localAcceptanceThreshold (radius gradientBound c₁ c₂ sigma L : ℝ) : ℝ :=
  min (radius / (2 * c₂ * gradientBound)) (2 * (1 - sigma) * c₁ / (L * c₂ ^ 2))

/-- Every sufficiently small positive safeguarded trial remains in the
local ball and passes the actual Armijo test. -/
theorem local_accepted_of_step_le (f : E → ℝ) (G : E → E) (center : E) (radius : ℝ)
    (hF : ∀ z ∈ ball center radius, HasFDerivAt f (innerSL ℝ (G z)) z)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzOnWith L G (ball center radius))
    (c₁ c₂ sigma gradientBound : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hsigma : sigma < 1) (x u : E) (hx : x ∈ ball center (radius / 2))
    (hg : G x ≠ 0) (hgrad : ‖G x‖ ≤ gradientBound)
    (hu : GradientRelated c₁ c₂ (G x) u) (t : ℝ) (ht : 0 < t)
    (hbound : t ≤ localAcceptanceThreshold radius gradientBound c₁ c₂ sigma L)
    (hgradientBound : 0 < gradientBound) : Accepted f sigma x (G x) u t := by
  have hball := hbound.trans (min_le_left _ _)
  have htime := hbound.trans (min_le_right _ _)
  have hlen : t * ‖u‖ ≤ radius / 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hu.2 ht.le
    have h₂ := mul_le_mul_of_nonneg_left hgrad (mul_nonneg ht.le hc₂.le)
    have h₃ := (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hc₂) hgradientBound)).mp hball
    nlinarith
  have hxs : x + t • u ∈ ball center radius := by
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have hn := norm_add_le (x - center) (t • u)
    rw [norm_smul, Real.norm_of_nonneg ht.le] at hn
    have he : x + t • u - center = (x - center) + t • u := by abel
    rw [he]
    linarith
  have hradius : 0 < radius := by have := (dist_nonneg : 0 ≤ dist x center); rw [mem_ball] at hx; linarith
  have hx' : x ∈ ball center radius := by rw [mem_ball] at hx ⊢; linarith
  have hn : 0 < ‖G x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hs : inner ℝ (G x) u < 0 := hu.1.trans_lt (by nlinarith)
  apply (accepted_iff_armijo f sigma x (G x) u t ht hs).2
  have hd := (abs_le.mp (descent_lemma_on_ball f G center radius hF L hG x (t • u) hx' hxs)).2
  rw [inner_smul_right, norm_smul, Real.norm_of_nonneg ht.le] at hd
  have hsq : ‖u‖ ^ 2 ≤ c₂ ^ 2 * ‖G x‖ ^ 2 := by
    nlinarith [hu.2, norm_nonneg u, norm_nonneg (G x), sq_nonneg (c₂ * ‖G x‖ - ‖u‖)]
  have htime' : (L : ℝ) * c₂ ^ 2 * t ≤ 2 * (1 - sigma) * c₁ :=
    by simpa only [mul_comm] using (le_div_iff₀ (mul_pos hL (sq_pos_of_pos hc₂))).mp htime
  have hcurv : (L : ℝ) * (t * ‖u‖) ^ 2 / 2 ≤ (1 - sigma) * c₁ * t * ‖G x‖ ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hsq (mul_nonneg hL.le (sq_nonneg t))
    have h₂ := mul_le_mul_of_nonneg_right htime' (mul_nonneg ht.le hn.le)
    nlinarith
  have hgrad' := mul_le_mul_of_nonneg_left hu.1 (mul_nonneg (sub_nonneg.mpr hsigma.le) ht.le)
  nlinarith

/-- The actual one-probe search is accepted and has a uniform positive
lower step bound derived solely from local function/gradient data. -/
theorem outerSearch_local_accepted_lower (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (center : E) (radius : ℝ) (hradius : 0 < radius)
    (hF : ∀ z ∈ ball center radius, HasFDerivAt f (innerSL ℝ (G z)) z)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzOnWith L G (ball center radius))
    (sigma : ℝ) (hsigma : sigma < 1) (gradientBound : ℝ) (hgradientBound : 0 < gradientBound)
    (S : State E) (hx : S.point ∈ ball center (radius / 2))
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant)
    (hcache : S.gradient = G S.point) (hg : S.gradient ≠ 0) (hgrad : ‖S.gradient‖ ≤ gradientBound) :
    Accepted f sigma S.point S.gradient (outerSearch model f G sigma S).direction
        (outerSearch model f G sigma S).length ∧
      min 1 (localAcceptanceThreshold radius gradientBound S.descentConstant S.normConstant sigma L / 10) ≤
        (outerSearch model f G sigma S).length := by
  classical
  have hc₂pos : 0 < S.normConstant := hc₁.trans_le hc₂
  have hthreshold : 0 < localAcceptanceThreshold radius gradientBound S.descentConstant S.normConstant sigma L := by
    unfold localAcceptanceThreshold
    positivity
  unfold outerSearch
  dsimp only
  split
  · exact ⟨by assumption, min_le_left _ _⟩
  · let M₀ := model S
    let S₁ := { M₀.updateState S with
      pairs := appendPositive M₀.pairs (observedTrialPair f G S (M₀.safeDirection S)) }
    let u := (model S₁).safeDirection S₁
    have hu : GradientRelated S.descentConstant S.normConstant S.gradient u :=
      safeguard_gradientRelated _ _ _ hc₁ hc₂ _ _
    have hsmall (t : ℝ) (ht : 0 < t)
        (hb : t ≤ localAcceptanceThreshold radius gradientBound S.descentConstant S.normConstant sigma L) :
        Accepted f sigma S.point S.gradient u t := by
      rw [hcache] at hu hg hgrad ⊢
      exact local_accepted_of_step_le f G center radius hF L hL hG _ _ sigma gradientBound
        hc₁ hc₂pos hsigma _ _ hx hg hgrad hu t ht hb hgradientBound
    have hb := backtracking_threshold f sigma S.point S.gradient u _ hthreshold hsmall
    exact ⟨(backtrackingIndex_spec f sigma S.point S.gradient u hb.1).1, hb.2⟩

end
end krylov.XR
