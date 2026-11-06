import nesterov.FiniteCondition.TongueFree

/-! Article: Theorem `thm:tonguefree` (b,c). Strict counterexamples are produced
inside the original stable range, retaining positive lower curvature. -/
namespace nesterov.FiniteCondition
noncomputable section
open nesterov.TwoStep Set Filter
open scoped Topology

private theorem perturb_negative {β τ ξ : ℝ} (hβ : 0≤β) (hτ : 0≤τ)
    (hn : Ltau β τ 0 (maxStep β τ) ξ<0) :
    ∃ yμ y : ℝ,0<yμ ∧ yμ<y ∧ y<maxStep β τ ∧ Ltau β τ yμ y ξ<0 := by
  have hm := maxStep_pos hβ hτ
  have hc : Continuous (fun y : ℝ=>Ltau β τ 0 y ξ) := by unfold Ltau A0 A1 A2;fun_prop
  have he : ∀ᶠ y in 𝓝[<] (maxStep β τ),Ltau β τ 0 y ξ<0 :=
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hn)
  have hI : ∀ᶠ y in 𝓝[<] (maxStep β τ),y∈Ioo 0 (maxStep β τ) := Ioo_mem_nhdsLT hm
  obtain ⟨y,hy,hn⟩ := (hI.and he).exists
  have hcμ : Continuous (fun yμ : ℝ=>Ltau β τ yμ y ξ) := by unfold Ltau A0 A1 A2;fun_prop
  have heμ : ∀ᶠ yμ in 𝓝[>] (0:ℝ),Ltau β τ yμ y ξ<0 :=
    (hcμ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hn)
  have hIμ : ∀ᶠ yμ in 𝓝[>] (0:ℝ),yμ∈Ioo 0 y := Ioo_mem_nhdsGT hy.1
  obtain ⟨yμ,hμ,hneg⟩ := (hIμ.and heμ).exists
  exact ⟨yμ,y,hμ.1,hμ.2,hy.2,hneg⟩

theorem three_tongue_negative {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht : τ<tauThree β) :
    ∃ μ L : ℝ,0<μ ∧ μ<L ∧ Quadratic.Stable μ L β τ 1 ∧ Ltau β τ μ L (3/2)<0 := by
  have hn : Ltau β τ 0 (maxStep β τ) (3/2)<0 := by
    rw [Ltau_maxStep (by positivity : 1+2*τ≠0),boundaryFactor_three_halves]
    exact mul_neg_of_pos_of_neg (div_pos (by norm_num) (by positivity))
      (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr ht))
  obtain ⟨μ,L,hμ,hL,hm,hn⟩ := perturb_negative hβ hτ hn
  refine ⟨μ,L,hμ,hL,?_,hn⟩
  apply (Quadratic.stable_iff hμ hL (by norm_num) hβ hβ1 hτ).mpr
  have hh := (lt_div_iff₀ (show 0<1+2*τ by positivity)).mp hm
  simpa only [one_mul] using hh

theorem lagOne_negative {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht : τ<tauStar β) :
    ∃ μ L ξ : ℝ,0<μ ∧ μ<L ∧ Quadratic.Stable μ L β τ 1 ∧
      ξ∈Ioo (0:ℝ) 2 ∧ Ltau β τ μ L ξ<0 := by
  have hb : boundaryFactor β τ 2<0 := by
    rw [boundaryFactor_two]
    exact mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr ht)
  have hc : Continuous (fun ξ : ℝ=>boundaryFactor β τ ξ) := by unfold boundaryFactor;fun_prop
  have he : ∀ᶠ ξ in 𝓝[<] (2:ℝ),boundaryFactor β τ ξ<0 :=
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hb)
  have hI : ∀ᶠ ξ in 𝓝[<] (2:ℝ),ξ∈Ioo 0 2 := Ioo_mem_nhdsLT (by norm_num)
  obtain ⟨ξ,hξ,hn⟩ := (hI.and he).exists
  have hnL : Ltau β τ 0 (maxStep β τ) ξ<0 := by
    rw [Ltau_maxStep (by positivity : 1+2*τ≠0)]
    exact mul_neg_of_pos_of_neg (div_pos (by linarith [hξ.2]) (by positivity)) hn
  obtain ⟨μ,L,hμ,hL,hm,hn⟩ := perturb_negative hβ hτ hnL
  refine ⟨μ,L,ξ,hμ,hL,?_,hξ,hn⟩
  apply (Quadratic.stable_iff hμ hL (by norm_num) hβ hβ1 hτ).mpr
  have hh := (lt_div_iff₀ (show 0<1+2*τ by positivity)).mp hm
  simpa only [one_mul] using hh

theorem three_tongue_witness {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht : τ<tauThree β) :
    ∃ (q : Momentum.Tuning) (μ L : ℝ),q.beta=β ∧ q.tau=τ ∧ q.stepSize=1 ∧
      0<μ ∧ μ<L ∧ q.Stable μ L ∧ Phase.momentumAngle q μ L (2*Real.pi/3)<Real.pi/3 ∧
      1<Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  obtain ⟨μ,L,hμ,hL,hs,hn⟩ := three_tongue_negative hβ hβ1 hτ ht
  let q : Momentum.Tuning := ⟨β,τ,1,hβ,hβ1,hτ,by norm_num⟩
  have hcos : 1-Real.cos (2*Real.pi/3)=(3:ℝ)/2 := by
    rw [show 2*Real.pi/3=2*(Real.pi/3) by ring,Real.cos_two_mul,Real.cos_pi_div_three]
    norm_num
  have hnq : Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos (2*Real.pi/3))<0 := by
    simpa only [q,hcos,one_mul] using hn
  have hs' : q.Stable μ L := hs
  have hp := ((stable_Ltau_phase_sign q hμ hL hs'
    ⟨by positivity,by linarith [Real.pi_pos]⟩).2.2.mp hnq)
  have ha : Phase.momentumAngle q μ L (2*Real.pi/3)<Real.pi/3 := by linarith
  exact ⟨q,μ,L,rfl,rfl,rfl,hμ,hL,hs',ha,
    negative_Ltau_restRate q hμ hL hs' (K:=3) le_rfl (by simpa using hnq)⟩

end
end nesterov.FiniteCondition
