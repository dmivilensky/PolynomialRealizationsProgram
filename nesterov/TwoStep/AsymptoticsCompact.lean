import nesterov.TwoStep.AsymptoticsBasics
import nesterov.TwoStep.AsymptoticsModel
import Mathlib.Topology.Sequences

/-! Lemma accel(b): every accelerated sequence has a physical slow-data subsequence. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

theorem accelerated_theta_lower (q : Momentum.Tuning) {ε c : ℝ}
    (hε : 0<ε) (hε1 : ε<1) (_hc : 0<c) (hstable : q.Stable (ε^2) 1)
    (hrate : Quadratic.quadraticRate (ε^2) 1 q.beta q.tau q.stepSize≤1-c*ε) :
    2*c-(c^2+2)*ε≤(1-q.beta)/ε := by
  have hμ : 0<ε^2 := sq_pos_of_pos hε
  have hμL : ε^2<1 := by nlinarith
  have hρ := Quadratic.quadraticRate_nonneg_general (β:=q.beta) (τ:=q.tau) (h:=q.stepSize) hμL.le
  have hr : 0≤1-c*ε := hρ.trans hrate
  have hsq := (sq_le_sq₀ hρ hr).mpr hrate
  have hq := (Quadratic.endpoint_rate_bounds hμL.le hstable).2.2
  have hm := (q.stable_iff hμ hμL).mp hstable
  simp only [mul_one] at hm
  have hyt : q.stepSize*q.tau<2 := by nlinarith [q.step_pos,q.beta_lt_one]
  apply (le_div_iff₀ hε).mpr
  nlinarith [mul_le_mul_of_nonneg_right hyt.le hμ.le]

/-- The extracted family retains the exact accelerated tunings along its subsequence. -/
theorem accelerated_subsequence {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n) :
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ ∃ θ y τ : ℝ,
      2*c≤θ ∧ c^2≤y ∧ 0≤τ ∧ y*(1+2*τ)≤4 ∧
      ∃ F : Scaling ℕ atTop θ y τ,F.epsilon=ε ∘ φ ∧ F.tuning=q ∘ φ := by
  let M : ℝ := max 4 (8/c)
  let x : ℕ→ℝ × (ℝ × ℝ) := fun n=>((1-(q n).beta)/ε n,((q n).stepSize,(q n).tau))
  let K : Set (ℝ × (ℝ × ℝ)) := Icc 0 M ×ˢ (Icc (c^2) 4 ×ˢ Icc 0 (2/c^2))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hepos : ∀ᶠ n in atTop,0<ε n := he.eventually self_mem_nhdsWithin
  have hesmall : ∀ᶠ n in atTop,ε n<1 :=
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  have hx : ∀ᶠ n in atTop,x n∈K := by
    filter_upwards [hepos,hesmall,hstable,hrate] with n hn hn1 hs hr
    obtain ⟨hy,hy4,ht,hβ⟩ := accelerated_tuning_bounds (q n) hn hn1 hc hs hr
    refine ⟨⟨div_nonneg (by linarith [(q n).beta_lt_one]) hn.le,?_⟩,
      ⟨hy,hy4.le⟩,⟨(q n).tau_nonneg,ht.le⟩⟩
    exact (div_le_iff₀ hn).mpr hβ.le
  obtain ⟨p,hp,φ,hφ,ht⟩ := hK.tendsto_subseq' hx.frequently
  have htθ : Tendsto (fun n=>(1-(q (φ n)).beta)/ε (φ n)) atTop (𝓝 p.1) := by
    exact (continuous_fst.tendsto p).comp ht
  have hty : Tendsto (fun n=>(q (φ n)).stepSize) atTop (𝓝 p.2.1) := by
    exact (continuous_fst.tendsto p.2).comp ((continuous_snd.tendsto p).comp ht)
  have htτ : Tendsto (fun n=>(q (φ n)).tau) atTop (𝓝 p.2.2) := by
    exact (continuous_snd.tendsto p.2).comp ((continuous_snd.tendsto p).comp ht)
  have heφ := he.comp hφ.tendsto_atTop
  have hθbound : 2*c≤p.1 := by
    have hl : Tendsto (fun n=>2*c-(c^2+2)*ε (φ n)) atTop (𝓝 (2*c)) := by
      simpa only [Function.comp_def,mul_zero,sub_zero] using
        (tendsto_const_nhds (x:=2*c)).sub ((heφ.mono_right nhdsWithin_le_nhds).const_mul (c^2+2))
    apply le_of_tendsto_of_tendsto hl htθ
    filter_upwards [hφ.tendsto_atTop.eventually hepos,hφ.tendsto_atTop.eventually hesmall,
      hφ.tendsto_atTop.eventually hstable,hφ.tendsto_atTop.eventually hrate]
      with n hn hn1 hs hr
    exact accelerated_theta_lower (q (φ n)) hn hn1 hc hs hr
  have hmargin : p.2.1*(1+2*p.2.2)≤4 := by
    have hml := hty.mul ((tendsto_const_nhds (x:=(1:ℝ))).add (htτ.const_mul 2))
    apply le_of_tendsto hml
    filter_upwards [hφ.tendsto_atTop.eventually hepos,hφ.tendsto_atTop.eventually hesmall,
      hφ.tendsto_atTop.eventually hstable] with n hn hn1 hs
    have hm := ((q (φ n)).stable_iff (sq_pos_of_pos hn) (by nlinarith : ε (φ n)^2<1)).mp hs
    simp only [mul_one] at hm
    exact (hm.trans (by linarith [(q (φ n)).beta_lt_one])).le
  let F : Scaling ℕ atTop p.1 p.2.1 p.2.2 := {
    epsilon := ε ∘ φ
    tuning := q ∘ φ
    epsilon_tendsto := heφ
    theta_tendsto := htθ
    step_tendsto := hty
    tau_tendsto := htτ
    theta_pos := (mul_pos (by norm_num) hc).trans_le hθbound
    step_pos := (sq_pos_of_pos hc).trans_le hp.2.1.1
    tau_nonneg := hp.2.2.1 }
  exact ⟨φ,hφ,p.1,p.2.1,p.2.2,hθbound,hp.2.1.1,hp.2.2.1,hmargin,F,rfl,rfl⟩

end
end nesterov.TwoStep
