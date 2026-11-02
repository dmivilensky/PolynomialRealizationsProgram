import krylov.XR.LocalAcceptance
import krylov.XR.Global

/-!
Article: main_krylov, G1 and thm:grow, stationarity of the accepted limit.
Use: justify G(x*)=0 from the original local hypotheses and literal
safeguarded Armijo execution. No global Lipschitz condition is introduced.
Source: a uniform local sufficient-acceptance threshold, actual clipped
backtracking and continuity of the converging accepted function values.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual sufficient decrease on the local tail, including the stopped
branch and the one rejected-probe reset. -/
theorem outerAdvance_local_decrease (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (center : E) (radius : ℝ) (hradius : 0 < radius)
    (hF : ∀ z ∈ ball center radius, HasFDerivAt f (innerSL ℝ (G z)) z)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzOnWith L G (ball center radius))
    (gradientBound : ℝ) (hgradientBound : 0 < gradientBound)
    (hsigma : 0 < P.armijo) (hsigma₁ : P.armijo < 1) (S : State E)
    (hx : S.point ∈ ball center (radius / 2))
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point) (hgrad : ‖S.gradient‖ ≤ gradientBound) :
    (outerAdvance P dimension model f G S).value ≤ S.value -
      P.armijo * min 1 (localAcceptanceThreshold radius gradientBound S.descentConstant
        S.normConstant P.armijo L / 10) * S.descentConstant * ‖S.gradient‖ ^ 2 := by
  classical
  by_cases hzero : S.gradient = 0
  · simp [outerAdvance, hzero]
  · let R := outerSearch model f G P.armijo S
    have hr := outerSearch_gradientRelated model f G P.armijo S hc₁ hc₂
    have ht := outerSearch_length_pos model f G P.armijo S
    have hlocal := outerSearch_local_accepted_lower model f G center radius hradius hF L hL hG
      P.armijo hsigma₁ gradientBound hgradientBound S hx hc₁ hc₂ hg hzero hgrad
    have hn : 0 < ‖S.gradient‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzero)
    have hs : inner ℝ S.gradient R.direction < 0 := hr.1.trans_lt (by nlinarith)
    have harm := (accepted_iff_armijo f P.armijo S.point S.gradient R.direction R.length ht hs).1 hlocal.1
    rw [← hf] at harm
    simp only [outerAdvance, ite_eq_right hzero]
    change f (S.point + R.length • R.direction) ≤ _
    have hgrad' := mul_le_mul_of_nonneg_left hr.1 (mul_nonneg hsigma.le ht.le)
    have hlength := mul_le_mul_of_nonneg_right hlocal.2
      (mul_nonneg (mul_nonneg hsigma.le hc₁.le) hn.le)
    nlinarith

/-- The true gradient at a converging accepted limit is zero under purely
local smoothness. This discharges the critical-point fact needed to bound
all genuine trial queries by O(distance to the limit). -/
theorem run_local_limit_stationary (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (S₀ : State E) (hf₀ : S₀.value = f S₀.point) (hg₀ : S₀.gradient = G S₀.point)
    (hc₁ : 0 < S₀.descentConstant) (hc₂ : S₀.descentConstant ≤ S₀.normConstant)
    (hsigma : 0 < P.armijo) (hsigma₁ : P.armijo < 1)
    (center : E) (radius : ℝ) (hradius : 0 < radius)
    (hF : ∀ z ∈ ball center radius, HasFDerivAt f (innerSL ℝ (G z)) z)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzOnWith L G (ball center radius))
    (hconv : Tendsto (fun k => (run P dimension model f G S₀ k).point) atTop (𝓝 center)) : G center = 0 := by
  let states := run P dimension model f G S₀
  let bound := ‖G center‖ + 1
  let threshold := localAcceptanceThreshold radius bound S₀.descentConstant S₀.normConstant P.armijo L
  let C := P.armijo * min 1 (threshold / 10) * S₀.descentConstant
  have hbound : 0 < bound := by dsimp only [bound]; positivity
  have hc₂pos : 0 < S₀.normConstant := hc₁.trans_le hc₂
  have hthreshold : 0 < threshold := by dsimp only [threshold, localAcceptanceThreshold]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hcenter : center ∈ ball center radius := mem_ball_self hradius
  have hfc : ContinuousAt f center := (hF center hcenter).continuousAt
  have hGc : ContinuousAt G center := (hG.continuousOn center hcenter).continuousAt (isOpen_ball.mem_nhds hcenter)
  have hflim : Tendsto (fun k => f (states k).point) atTop (𝓝 (f center)) := hfc.tendsto.comp hconv
  have hglim : Tendsto (fun k => G (states k).point) atTop (𝓝 (G center)) := hGc.tendsto.comp hconv
  have hdiff : Tendsto (fun k => f (states (k + 1)).point - f (states k).point) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using (hflim.comp (tendsto_add_atTop_nat 1)).sub hflim
  have hright : Tendsto (fun k => -C * ‖G (states k).point‖ ^ 2) atTop (𝓝 (-C * ‖G center‖ ^ 2)) :=
    tendsto_const_nhds.mul (hglim.norm.pow 2)
  have hnear : ∀ᶠ k in atTop, (states k).point ∈ ball center (radius / 2) :=
    hconv.eventually (ball_mem_nhds center (by linarith))
  have hbounded : ∀ᶠ k in atTop, ‖G (states k).point‖ ≤ bound := by
    have hstrict : ‖G center‖ < bound := by dsimp only [bound]; linarith
    exact (hglim.norm.eventually (gt_mem_nhds hstrict)).mono (fun _ h => h.le)
  have hinequality : ∀ᶠ k in atTop,
      f (states (k + 1)).point - f (states k).point ≤ -C * ‖G (states k).point‖ ^ 2 := by
    filter_upwards [hnear, hbounded] with k hx hb
    have hc := run_cache_constants P dimension model f G S₀ hf₀ hg₀ k
    have hn := run_cache_constants P dimension model f G S₀ hf₀ hg₀ (k + 1)
    have h := outerAdvance_local_decrease P dimension model f G center radius hradius hF L hL hG
      bound hbound hsigma hsigma₁ (states k) hx (by rw [hc.2.2.1]; exact hc₁)
      (by rw [hc.2.2.1, hc.2.2.2]; exact hc₂) hc.1 hc.2.1 (by rw [hc.2.1]; exact hb)
    change (states (k + 1)).value ≤ _ at h
    rw [hn.1, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] at h
    change _ ≤ _ - C * ‖G (states k).point‖ ^ 2 at h
    linarith
  have hlim : 0 ≤ -C * ‖G center‖ ^ 2 := le_of_tendsto_of_tendsto hdiff hright hinequality
  by_contra hn
  have hp : 0 < C * ‖G center‖ ^ 2 := mul_pos hC (sq_pos_of_pos (norm_pos_iff.mpr hn))
  nlinarith

end
end krylov.XR
