import nesterov.Layer.Upper
import nesterov.Layer.ResultsLower
import nesterov.Layer.Divergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! The exact all-family acceleration criterion in the half-step layer. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

def layerAccelerated : Prop :=
  ∃ c : ℝ,0<c ∧ ∀ᶠ a in l,
    Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.tuning a).step_pos.ne' (F.epsilon a^2) 1≤1-c*F.epsilon a

private theorem rest_upper_of_full {c : ℝ}
    (hfull : ∀ᶠ a in l,
      Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1≤1-c*F.epsilon a) :
    ∀ᶠ a in l,
      Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1≤1-c*F.epsilon a := by
  filter_upwards [hfull,F.epsilon_pos,F.epsilon_zero.eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a ha he he1
  exact (Momentum.restRate_le_momentumRate (β:=(F.tuning a).beta) (τ:=(F.tuning a).tau)
    (F.tuning a).step_pos.ne' (sq_pos_of_pos he) (by nlinarith : F.epsilon a^2<1)).trans ha

theorem not_layerAccelerated_of_rest_growth [NeBot l]
    (hgrowth : ∀ᶠ a in l,1<Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1) :
    ¬F.layerAccelerated := by
  rintro ⟨c,hc,hfull⟩
  obtain ⟨a,ha,hu,he⟩ := (hgrowth.and ((F.rest_upper_of_full hfull).and F.epsilon_pos)).exists
  nlinarith [mul_pos hc he]

theorem not_layerAccelerated_of_deficit_limit [NeBot l] (hy2 : y<2)
    {B : ℝ} (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hBA : Layer.Astar θ y≤B)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ¬F.layerAccelerated := by
  have hBp : 0<B := (Layer.Astar_pos F.theta_pos F.step_pos hy2).trans_le hBA
  have hLambda : Layer.Lambda θ y B≤0 := by
    have hh := Layer.Lambda_antitone (θ:=θ) F.step_pos hy2 hBA
    simpa only [Layer.Lambda_at_Astar F.theta_pos F.step_pos hy2] using hh
  rintro ⟨c,hc,hfull⟩
  have hlow := F.layer_lower hy2 hBp hB hstable (c:=c/2)
    (by rw [max_eq_right hLambda,zero_div];linarith)
  obtain ⟨a,ha,hu,he⟩ := (hlow.and ((F.rest_upper_of_full hfull).and F.epsilon_pos)).exists
  nlinarith [ha.2,mul_pos hc he]

theorem not_layerAccelerated_of_deficit_atTop [NeBot l] (hy2 : y<2)
    (hB : Tendsto F.layerDeficit l atTop)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ¬F.layerAccelerated := by
  have hd := (F.layer_divergence_above hy2 (B:=Layer.Astar θ y+1) (by linarith)
    (hB.eventually_ge_atTop _) hstable).2
  apply F.not_layerAccelerated_of_rest_growth
  exact hd.mono fun a ha=>ha.2.2.2

/-- A strict extended-real limsup bound gives a uniform lag-one certificate;
the actual layer coordinate need not converge or have a lower bound. -/
theorem layerAccelerated_of_limsup_lt (hy2 : y<2)
    (hlim : limsup (fun a=>(F.layerDeficit a:EReal)) l<(Layer.Astar θ y:EReal)) :
    F.layerAccelerated := by
  obtain ⟨B,hBlim,hBA⟩ := EReal.exists_between_coe_real hlim
  have hB : ∀ᶠ a in l,F.layerDeficit a≤B := by
    have hh := eventually_lt_of_limsup_lt hBlim (by isBoundedDefault)
    exact hh.mono fun a ha=>(EReal.coe_lt_coe_iff.mp ha).le
  have hBA' : B<Layer.Astar θ y := EReal.coe_lt_coe_iff.mp hBA
  have hpos := (Layer.constant_pos_iff F.theta_pos F.step_pos hy2).mpr hBA'
  refine ⟨Layer.constant θ y B/2,by linarith,?_⟩
  exact (F.layer_upper_of_deficit_le hy2 hB hBA' (by linarith)).mono fun _ h=>h.le

theorem acceleration_deficit_eventually_bounded [NeBot l] (hy2 : y<2)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hacc : F.layerAccelerated) :
    ∀ᶠ a in l,F.layerDeficit a<Layer.Astar θ y+1 := by
  by_contra hn
  have hbad : ∃ᶠ a in l,Layer.Astar θ y+1≤F.layerDeficit a := by
    simpa only [not_eventually,not_lt] using hn
  let m : Filter A := l⊓𝓟 {a | Layer.Astar θ y+1≤F.layerDeficit a}
  let : NeBot m := frequently_iff_neBot.mp hbad
  have hml : Tendsto (id : A→A) m l := tendsto_id.mono_left inf_le_left
  let G := F.reindex id hml
  have hGs : ∀ᶠ a in m,(G.tuning a).Stable (G.epsilon a^2) 1 := by
    simpa only [G,reindex,Function.comp_def,id_eq] using hml.eventually hstable
  have hGB : ∀ᶠ a in m,Layer.Astar θ y+1≤G.layerDeficit a := by
    have hh : ∀ᶠ a in m,Layer.Astar θ y+1≤F.layerDeficit a := by
      exact eventually_inf_principal.mpr (Eventually.of_forall fun _ ha=>ha)
    simpa only [G,layerDeficit,reindex,Function.comp_def,id_eq] using hh
  have hGa : G.layerAccelerated := by
    obtain ⟨c,hc,hfull⟩ := hacc
    refine ⟨c,hc,?_⟩
    simpa only [G,reindex,Function.comp_def,id_eq] using hml.eventually hfull
  have hgrowth := (G.layer_divergence_above hy2 (B:=Layer.Astar θ y+1) (by linarith) hGB hGs).2
  exact G.not_layerAccelerated_of_rest_growth (hgrowth.mono fun _ h=>h.2.2.2) hGa

include F in
private theorem exists_near_threshold (hy2 : y<2) {c : ℝ} (hc : 0<c) :
    ∃ B : ℝ,0<B ∧ B<Layer.Astar θ y ∧ max (Layer.Lambda θ y B) 0/3<c := by
  have hg : Continuous (fun B : ℝ=>max (Layer.Lambda θ y B) 0/3) :=
    ((Layer.continuous_Lambda θ y).max continuous_const).div_const 3
  have ht : Tendsto (fun B : ℝ=>max (Layer.Lambda θ y B) 0/3)
      (𝓝[<] (Layer.Astar θ y)) (𝓝 0) := by
    simpa only [Layer.Lambda_at_Astar F.theta_pos F.step_pos hy2,max_self,zero_div] using
      (hg.tendsto (Layer.Astar θ y)).mono_left nhdsWithin_le_nhds
  have hp : ∀ᶠ B in 𝓝[<] (Layer.Astar θ y),0<B :=
    (eventually_gt_nhds (Layer.Astar_pos F.theta_pos F.step_pos hy2)).filter_mono nhdsWithin_le_nhds
  obtain ⟨B,hsmall,hp,hbelow⟩ := ((ht.eventually (eventually_lt_nhds hc)).and
    (hp.and self_mem_nhdsWithin)).exists
  exact ⟨B,hp,hbelow,hsmall⟩

/-- Acceleration forces a uniform strict gap from the layer threshold.
No upper bound or limit of the original deficit is assumed. -/
theorem layer_limsup_lt_of_accelerated [l.IsCountablyGenerated] [NeBot l]
    (hy2 : y<2)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hacc : F.layerAccelerated) :
    limsup (fun a=>(F.layerDeficit a:EReal)) l<(Layer.Astar θ y:EReal) := by
  obtain ⟨c,hc,hfull⟩ := hacc
  obtain ⟨B₀,hB₀p,hB₀A,hB₀c⟩ := F.exists_near_threshold hy2 (by linarith : 0<c/2)
  have hbounded := F.acceleration_deficit_eventually_bounded hy2 hstable ⟨c,hc,hfull⟩
  have hevent : ∀ᶠ a in l,F.layerDeficit a≤B₀ := by
    by_contra hn
    have hbad : ∃ᶠ a in l,B₀<F.layerDeficit a := by
      simpa only [not_eventually,not_le] using hn
    obtain ⟨s,hsl,hbs⟩ := exists_seq_forall_of_frequently hbad
    have hmem : ∀ᶠ n : ℕ in atTop,F.layerDeficit (s n)∈Icc B₀ (Layer.Astar θ y+1) := by
      filter_upwards [hsl.eventually hbounded] with n hn
      exact ⟨(hbs n).le,hn.le⟩
    obtain ⟨B,hBK,φ,hφ,hT⟩ := isCompact_Icc.tendsto_subseq' hmem.frequently
    have hsφ : Tendsto (fun n=>s (φ n)) atTop l := hsl.comp hφ.tendsto_atTop
    let G := F.reindex (fun n=>s (φ n)) hsφ
    have hGB : Tendsto G.layerDeficit atTop (𝓝 B) := by
      change Tendsto (fun n=>F.layerDeficit (s (φ n))) atTop (𝓝 B)
      simpa only [Function.comp_def] using hT
    have hGs : ∀ᶠ n in atTop,(G.tuning n).Stable (G.epsilon n^2) 1 := by
      simpa only [G,reindex,Function.comp_def] using hsφ.eventually hstable
    have hGfull : ∀ᶠ n in atTop,
        Momentum.momentumRate (G.tuning n).beta (G.tuning n).tau (G.tuning n).stepSize
          (G.tuning n).step_pos.ne' (G.epsilon n^2) 1≤1-c*G.epsilon n := by
      simpa only [G,reindex,Function.comp_def] using hsφ.eventually hfull
    have hmax : max (Layer.Lambda θ y B) 0≤max (Layer.Lambda θ y B₀) 0 :=
      max_le_max (Layer.Lambda_antitone (θ:=θ) F.step_pos hy2 hBK.1) le_rfl
    have hthreshold : max (Layer.Lambda θ y B) 0/3<c/2 :=
      (div_le_div_of_nonneg_right hmax (by norm_num : (0:ℝ)≤3)).trans_lt hB₀c
    have hLower := G.layer_lower hy2 (hB₀p.trans_le hBK.1) hGB hGs hthreshold
    obtain ⟨n,hn,hu,he⟩ := (hLower.and ((G.rest_upper_of_full hGfull).and G.epsilon_pos)).exists
    nlinarith [hn.2,mul_pos hc he]
  have hbound : ∀ᶠ a in l,(F.layerDeficit a:EReal)≤(B₀:EReal) :=
    hevent.mono fun _ ha=>EReal.coe_le_coe_iff.mpr ha
  exact (Filter.limsup_le_of_le (by isBoundedDefault) hbound).trans_lt
    (EReal.coe_lt_coe_iff.mpr hB₀A)

/-- The full iff in Theorem layer, including arbitrary nonsmooth and
oscillating parameter families. -/
theorem layer_acceleration_iff [l.IsCountablyGenerated] [NeBot l]
    (hy2 : y<2)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    F.layerAccelerated ↔
      limsup (fun a=>(F.layerDeficit a:EReal)) l<(Layer.Astar θ y:EReal) :=
  ⟨F.layer_limsup_lt_of_accelerated hy2 hstable,F.layerAccelerated_of_limsup_lt hy2⟩

theorem layer_acceleration_iff_explicit [l.IsCountablyGenerated] [NeBot l]
    (hy2 : y<2)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    (∃ c : ℝ,0<c ∧ ∀ᶠ a in l,
      Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1≤1-c*F.epsilon a) ↔
      limsup (fun a=>(F.layerDeficit a:EReal)) l<(Layer.Astar θ y:EReal) :=
  F.layer_acceleration_iff hy2 hstable

end
end nesterov.TwoStep.Scaling
