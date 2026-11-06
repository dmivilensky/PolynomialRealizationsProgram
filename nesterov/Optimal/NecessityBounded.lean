import nesterov.Optimal.NecessityMargin
import nesterov.Corner.Optimality
import Mathlib.Topology.Sequences

/-! A positive ratio defect with bounded scaled deficit contradicts optimality. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable (F : Scaling ℕ atTop 3 2 (1/2))

private theorem defect_coordinates {A : Type*} {l : Filter A}
    (G : Scaling A l 3 2 (1/2)) : ∀ᶠ p in l,
    G.cornerA p=2*G.cornerAlpha p/(G.tuning p).stepSize ∧
    G.cornerB p=(G.stabilityMargin p-4*G.cornerAlpha p)/2 := by
  filter_upwards [G.epsilon_pos] with p hp
  unfold cornerA cornerB cornerAlpha stabilityMargin
  constructor
  · field_simp [(G.tuning p).step_pos.ne',hp.ne']
  · field_simp [hp.ne']
    ring

theorem corner_no_bounded_defect_bad_sequence {q M : ℝ} (hq : 0<q)
    (hstable : ∀ᶠ p in atTop,(F.tuning p).Stable (F.epsilon p^2) 1)
    (hfull : Tendsto F.fullCoefficientAt atTop (𝓝 1))
    (hlo : ∀ᶠ p in atTop,q≤F.cornerCriterionRatio p)
    (hbound : ∀ᶠ p in atTop,F.cornerDefect p≤M) : False := by
  have hM : 0≤M := by
    obtain ⟨p,hp⟩ := hbound.exists
    exact (F.corner_defect_nonneg p).trans hp
  have hbounds : ∀ᶠ p in atTop,
      (F.cornerDefect p,F.stabilityMargin p)∈Icc (0:ℝ) M ×ˢ Icc 4 (M^2/q) ∧
        9*q≤F.cornerDefect p^2 := by
    filter_upwards [hlo,hbound,F.corner_denominator_pos hstable,F.stable_iff_scaled_margin,hstable,
      F.theta_tendsto.eventually (eventually_gt_nhds (by norm_num : (2:ℝ)<3))]
      with p hr hd hD hs hstab ht
    change 2<F.thetaAt p at ht
    have hm : 4≤F.stabilityMargin p := by have h := hs.mp hstab;linarith
    have hd0 := F.corner_defect_nonneg p
    have hsq : F.cornerDefect p^2≤M^2 := by nlinarith
    have hqD : q*(F.stabilityMargin p+5+F.cornerDefect p)≤F.cornerDefect p^2 :=
      (le_div_iff₀ hD).mp hr
    have hmupper : F.stabilityMargin p≤M^2/q := (le_div_iff₀ hq).mpr (by nlinarith)
    exact ⟨⟨⟨hd0,hd⟩,⟨hm,hmupper⟩⟩,by nlinarith⟩
  have hK : IsCompact (Icc (0:ℝ) M ×ˢ Icc 4 (M^2/q)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨v,hv,s,hs,ht⟩ := hK.tendsto_subseq' (hbounds.mono fun _ h=>h.1).frequently
  let G : Scaling ℕ atTop 3 2 (1/2) := F.reindex s hs.tendsto_atTop
  have hd : Tendsto G.cornerDefect atTop (𝓝 v.1) := by
    exact (continuous_fst.tendsto v).comp ht
  have hm : Tendsto G.stabilityMargin atTop (𝓝 v.2) := by
    exact (continuous_snd.tendsto v).comp ht
  have hdp : 0<v.1 := by
    have hh : 9*q≤v.1^2 := ge_of_tendsto (hd.pow 2)
      (hs.tendsto_atTop.eventually (hbounds.mono fun _ h=>h.2))
    nlinarith [hv.1.1]
  have hα : Tendsto G.cornerAlpha atTop (𝓝 ((v.1+5)/4)) := by
    apply ((hd.add_const 5).div_const 4).congr'
    filter_upwards [hd.eventually (eventually_gt_nhds hdp)] with p hp
    have hp' : 0<4*G.cornerAlpha p-5 := by
      exact (lt_max_iff.mp hp).resolve_right (lt_irrefl 0)
    unfold cornerDefect
    rw [max_eq_left hp'.le]
    ring
  let a : ℝ := (v.1+5)/4
  let b : ℝ := (v.2-4*a)/2
  have hA : Tendsto G.cornerA atTop (𝓝 a) := by
    have h := (hα.const_mul 2).div G.step_tendsto (by norm_num : (2:ℝ)≠0)
    have hh : Tendsto (fun p=>2*G.cornerAlpha p/(G.tuning p).stepSize) atTop (𝓝 a) := by
      have hval : 2*((v.1+5)/4)/2=a := by dsimp [a];ring
      rw [hval] at h
      exact h
    exact hh.congr' ((defect_coordinates G).mono fun _ h=>h.1.symm)
  have hB : Tendsto G.cornerB atTop (𝓝 b) :=
    ((hm.sub (hα.const_mul 4)).div_const 2).congr' ((defect_coordinates G).mono fun _ h=>h.2.symm)
  have hGs : ∀ᶠ p in atTop,(G.tuning p).Stable (G.epsilon p^2) 1 :=
    hs.tendsto_atTop.eventually hstable
  have hGfull : Tendsto G.fullCoefficientAt atTop (𝓝 1) := hfull.comp hs.tendsto_atTop
  have hs7 : 7≤v.2 := by
    have hE := G.corner_margin_liminf_of_full_optimal hGs hGfull
    have hmE : Tendsto (fun p=>(G.stabilityMargin p:EReal)) atTop (𝓝 (v.2:EReal)) :=
      EReal.tendsto_coe.mpr hm
    rw [hmE.liminf_eq] at hE
    exact EReal.coe_le_coe_iff.mp hE
  have hmargin : (3:ℝ)<2*a+b := by dsimp [b];linarith
  have hw := (G.corner_optimal_iff hA hB hmargin).mp hGfull
  have ha := hw.2.1
  dsimp [a] at ha
  linarith

end
end nesterov.TwoStep.Scaling
