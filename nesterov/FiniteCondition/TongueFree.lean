import nesterov.FiniteCondition.Positivity
import nesterov.TwoStep.Phase

/-! Article: Theorem `thm:tonguefree` (a), with the literal finite-lag certificate. -/
namespace nesterov.FiniteCondition
noncomputable section
open nesterov.TwoStep Set

def chosenWeight (β τ : ℝ) : ℝ := if tauStar β≤τ then 0 else lagTwoWeight β τ

theorem stable_step_lt_maxStep (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) :
    q.stepSize*L<maxStep q.beta q.tau := by
  exact (lt_div_iff₀ (by linarith [q.tau_nonneg])).mpr ((q.stable_iff hμ hμL).mp hs)

theorem unit_xi {z : ℂ} (hz : ‖z‖=1) (hz1 : z≠1) : 1-z.re∈Ioc (0:ℝ) 2 := by
  have he : z.re^2+z.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simpa [Complex.normSq_apply,pow_two] using h
  have hr : z.re<1 := by
    have hle : z.re≤1 := by nlinarith [sq_nonneg (z.re-1),sq_nonneg z.im]
    apply lt_of_le_of_ne hle
    intro hh
    have hi : z.im=0 := by rw [hh] at he;nlinarith [sq_nonneg z.im]
    exact hz1 (Complex.ext (by simpa using hh) (by simpa using hi))
  exact ⟨by linarith,by nlinarith [sq_nonneg (z.re+1),sq_nonneg z.im]⟩

theorem tonguefree_multiplier (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (ht : tauThree q.beta≤q.tau) :
    0≤chosenWeight q.beta q.tau ∧
      ∀ z : ℂ,‖z‖=1 → z≠1 →
        0<(Quadratic.characteristic q.beta q.tau q.stepSize μ z*
          star (Quadratic.characteristic q.beta q.tau q.stepSize L z)*
          ((1-z)+(chosenWeight q.beta q.tau:ℂ)*(1-star z^2))).re := by
  have hy := stable_step_lt_maxStep q hμ hμL hs
  have hym : 0<q.stepSize*μ := mul_pos q.step_pos hμ
  have hμy : q.stepSize*μ<q.stepSize*L := mul_lt_mul_of_pos_left hμL q.step_pos
  by_cases hstar : tauStar q.beta≤q.tau
  · have hw : chosenWeight q.beta q.tau=0 := by simp [chosenWeight,hstar]
    refine ⟨by rw [hw],fun z hz hz1=>?_⟩
    rw [hw,Complex.ofReal_zero,zero_mul,add_zero,
      characteristic_unit_step q.beta q.tau q.stepSize μ,
      characteristic_unit_step q.beta q.tau q.stepSize L]
    have hns : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hz];norm_num
    have he := mixed_unit (β:=q.beta) (τ:=q.tau) (lam:=0)
      (yμ:=q.stepSize*μ) (y:=q.stepSize*L) hns
    simp only [Complex.ofReal_zero,zero_mul,add_zero,mixedPolynomial,mul_zero,
      one_mul,zero_mul,add_zero] at he
    rw [he]
    exact mul_pos (unit_xi hz hz1).1
      (lagOne_pos q.beta_nonneg q.beta_lt_one q.tau_nonneg hstar hym hμy hy (unit_xi hz hz1))
  · have hlt := lt_of_not_ge hstar
    have hw : chosenWeight q.beta q.tau=lagTwoWeight q.beta q.tau := by simp [chosenWeight,hstar]
    refine ⟨by rw [hw];exact (lagTwoWeight_pos q.beta_nonneg q.beta_lt_one q.tau_nonneg hlt).le,
      fun z hz hz1=>?_⟩
    rw [hw,characteristic_unit_step q.beta q.tau q.stepSize μ,
      characteristic_unit_step q.beta q.tau q.stepSize L]
    have hns : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hz];norm_num
    rw [mixed_unit hns]
    exact mul_pos (unit_xi hz hz1).1
      (mixed_pos q.beta_nonneg q.beta_lt_one q.tau_nonneg ht hlt hym hμy hy (unit_xi hz hz1))

theorem tonguefree_rate (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (ht : tauThree q.beta≤q.tau) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1 := by
  have hh := tonguefree_multiplier q hμ hμL hs ht
  exact Phase.momentumRate_lt_one_of_mixed q hμ hμL hs hh.1 hh.2

theorem lagOne_above_threshold (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (ht : tauStar q.beta≤q.tau) :
    ∀ ξ∈Ioc (0:ℝ) 2,0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) ξ := by
  intro ξ hξ
  exact lagOne_pos q.beta_nonneg q.beta_lt_one q.tau_nonneg ht
    (mul_pos q.step_pos hμ) (mul_lt_mul_of_pos_left hμL q.step_pos)
    (stable_step_lt_maxStep q hμ hμL hs) hξ

end
end nesterov.FiniteCondition
