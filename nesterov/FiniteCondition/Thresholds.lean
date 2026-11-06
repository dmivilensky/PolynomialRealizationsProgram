import nesterov.FiniteCondition.Counterexample

/-! Exact all-stable-tunings thresholds and the heavy-ball/Nesterov special cases. -/
namespace nesterov.FiniteCondition
noncomputable section
open nesterov.TwoStep Set

def AllStableTuningsConverge (β τ : ℝ) : Prop :=
  ∀ (h μ L : ℝ) (hh : 0<h),0<μ → μ<L → Quadratic.Stable μ L β τ h →
    Momentum.momentumRate β τ h hh.ne' μ L<1

def AllStableTuningsLagOne (β τ : ℝ) : Prop :=
  ∀ (h μ L : ℝ),0<h → 0<μ → μ<L → Quadratic.Stable μ L β τ h →
    ∀ ξ∈Ioc (0:ℝ) 2,0<Ltau β τ (h*μ) (h*L) ξ

theorem all_stable_converge_iff {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ) :
    AllStableTuningsConverge β τ ↔ tauThree β≤τ := by
  constructor
  · intro hall
    by_contra ht
    obtain ⟨q,μ,L,hqb,hqt,hqh,hμ,hL,hs,_,hr⟩ :=
      three_tongue_witness hβ hβ1 hτ (lt_of_not_ge ht)
    have hc := hall q.stepSize μ L q.step_pos hμ hL (by
      simpa only [Momentum.Tuning.Stable,hqb,hqt] using hs)
    have hb := Momentum.restRate_le_momentumRate (β:=q.beta) (τ:=q.tau) q.step_pos.ne' hμ hL
    rw [hqb,hqt] at hr hb
    linarith
  · intro ht h μ L hh hμ hL hs
    let q : Momentum.Tuning := ⟨β,τ,h,hβ,hβ1,hτ,hh⟩
    exact tonguefree_rate q hμ hL hs ht

theorem all_stable_lagOne_iff {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ) :
    AllStableTuningsLagOne β τ ↔ tauStar β≤τ := by
  constructor
  · intro hall
    by_contra ht
    obtain ⟨μ,L,ξ,hμ,hL,hs,hξ,hn⟩ := lagOne_negative hβ hβ1 hτ (lt_of_not_ge ht)
    have hp := hall 1 μ L (by norm_num) hμ hL hs ξ ⟨hξ.1,hξ.2.le⟩
    simp only [one_mul] at hp
    linarith
  · intro ht h μ L hh hμ hL hs ξ hξ
    let q : Momentum.Tuning := ⟨β,τ,h,hβ,hβ1,hτ,hh⟩
    exact lagOne_above_threshold q hμ hL hs ht ξ hξ

theorem tauThree_lt_tauStar {β : ℝ} (hβ : 0≤β) (hβ1 : β<1) : tauThree β<tauStar β := by
  have he := thresholds_gap β
  nlinarith

theorem tauStar_lt_half {β : ℝ} (hβ : 0≤β) (hβ1 : β<1) : tauStar β<1/2 := by
  unfold tauStar
  nlinarith

theorem tauStar_le_half_beta {β : ℝ} (hβ : 0≤β) (hβ1 : β<1) : tauStar β≤β/2 := by
  unfold tauStar
  nlinarith

theorem tauStar_le_beta {β : ℝ} (hβ : 0≤β) (hβ1 : β<1) : tauStar β≤β :=
  (tauStar_le_half_beta hβ hβ1).trans (by linarith)

theorem half_step_converges (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (ht : 1/2≤q.tau) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1 := by
  exact tonguefree_rate q hμ hμL hs
    ((tauThree_lt_tauStar q.beta_nonneg q.beta_lt_one).le.trans
      ((tauStar_lt_half q.beta_nonneg q.beta_lt_one).le.trans ht))

theorem nesterov_converges (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (ht : q.tau=q.beta) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1 := by
  apply tonguefree_rate q hμ hμL hs
  rw [ht]
  exact (tauThree_lt_tauStar q.beta_nonneg q.beta_lt_one).le.trans
    (tauStar_le_beta q.beta_nonneg q.beta_lt_one)

theorem heavyBall_three_threshold {β : ℝ} (hβ : 0≤β) :
    tauThree β≤0 ↔ β≤(Real.sqrt 13-3)/2 := by
  have hs : 0≤Real.sqrt 13 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  unfold tauThree
  constructor <;> intro hh <;> nlinarith

theorem heavyBall_lagOne_threshold {β : ℝ} (hβ : 0≤β) :
    tauStar β≤0 ↔ β≤Real.sqrt 5-2 := by
  have hs : 0≤Real.sqrt 5 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  unfold tauStar
  constructor <;> intro hh <;> nlinarith

theorem heavyBall_all_stable_iff {β : ℝ} (hβ : 0≤β) (hβ1 : β<1) :
    AllStableTuningsConverge β 0 ↔ β≤(Real.sqrt 13-3)/2 :=
  (all_stable_converge_iff hβ hβ1 le_rfl).trans (heavyBall_three_threshold hβ)

theorem heavyBall_all_stable_lagOne_iff {β : ℝ} (hβ : 0≤β) (hβ1 : β<1) :
    AllStableTuningsLagOne β 0 ↔ β≤Real.sqrt 5-2 :=
  (all_stable_lagOne_iff hβ hβ1 le_rfl).trans (heavyBall_lagOne_threshold hβ)

theorem tauThree_corner_expansion (θ ε : ℝ) :
    tauThree (1-θ*ε)=1/2-(5*θ/6)*ε+(θ^2/6)*ε^2 := by
  unfold tauThree
  ring

theorem tauStar_corner_expansion (θ ε : ℝ) :
    tauStar (1-θ*ε)=1/2-(3*θ/4)*ε+(θ^2/8)*ε^2 := by
  unfold tauStar
  ring

end
end nesterov.FiniteCondition
