import polyak.Levels.Chart.GapConnected
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact relative closure of the gap in its finite root coordinates. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set Filter Topology

def closedRootTriangle (K : ℕ) : Set ParameterSpace :=
  {p | boundaryCosine K≤p.2.1 ∧ p.2.1≤p.2.2 ∧ p.2.2≤boundaryCosine (K+1)}

theorem closure_gapParameterSet_subset (K : ℕ) :
    closure (gapParameterSet K)⊆closedRootTriangle K := by
  apply closure_minimal
  · intro p hp
    exact ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le⟩
  · exact (isClosed_le continuous_const (continuous_snd.fst)).inter
      ((isClosed_le (continuous_snd.fst) (continuous_snd.snd)).inter
        (isClosed_le (continuous_snd.snd) continuous_const))

def approachGap (K : ℕ) (p : ParameterSpace) (t : ℝ) : ParameterSpace :=
  let s₁ := (2*boundaryCosine K+boundaryCosine (K+1))/3
  let s₂ := (boundaryCosine K+2*boundaryCosine (K+1))/3
  let r₁ := (1-t)*p.2.1+t*s₁
  let r₂ := (1-t)*p.2.2+t*s₂
  (amplitudeFloor r₁ r₂+(p.1-amplitudeFloor p.2.1 p.2.2),r₁,r₂)

theorem approachGap_mem {K : ℕ} (hK : 2≤K) {p : ParameterSpace}
    (hp : p∈closedRootTriangle K) (ha : amplitudeFloor p.2.1 p.2.2<p.1)
    {t : ℝ} (ht : 0<t) (htu : t≤1) : approachGap K p t∈gapParameterSet K := by
  have hw := boundaryCosine_lt_succ hK
  have hnon : 0≤1-t := by linarith
  have h₁ : 0≤(1-t)*(p.2.1-boundaryCosine K) :=
    mul_nonneg hnon (sub_nonneg.mpr hp.1)
  have h₂ : 0≤(1-t)*(p.2.2-p.2.1) :=
    mul_nonneg hnon (sub_nonneg.mpr hp.2.1)
  have h₃ : 0≤(1-t)*(boundaryCosine (K+1)-p.2.2) :=
    mul_nonneg hnon (sub_nonneg.mpr hp.2.2)
  have hstrict : 0<t*(boundaryCosine (K+1)-boundaryCosine K)/3 :=
    div_pos (mul_pos ht (sub_pos.mpr hw)) (by norm_num)
  change _∧_∧_∧_
  dsimp [approachGap]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

theorem approachGap_tendsto {K : ℕ} {p : ParameterSpace}
    (hp : p∈closedRootTriangle K) (hK : 2≤K) :
    Tendsto (approachGap K p) (𝓝 (0:ℝ)) (𝓝 p) := by
  have h₁ : p.2.1<1 := hp.2.1.trans_lt (hp.2.2.trans_lt (boundaryCosine_succ_lt_one hK))
  have h₂ : p.2.2<1 := hp.2.2.trans_lt (boundaryCosine_succ_lt_one hK)
  have hlc : ContinuousAt (fun t : ℝ => (1-t)*p.2.1+
      t*((2*boundaryCosine K+boundaryCosine (K+1))/3)) 0 := by fun_prop
  have hrc : ContinuousAt (fun t : ℝ => (1-t)*p.2.2+
      t*((boundaryCosine K+2*boundaryCosine (K+1))/3)) 0 := by fun_prop
  have hc : ContinuousAt (approachGap K p) 0 := by
    have hd := ((show ContinuousAt (fun _ : ℝ => (1:ℝ)) 0 from continuousAt_const).sub hlc).mul
      ((show ContinuousAt (fun _ : ℝ => (1:ℝ)) 0 from continuousAt_const).sub hrc)
    have hn : (1-((1-(0:ℝ))*p.2.1+0*((2*boundaryCosine K+boundaryCosine (K+1))/3)))*
        (1-((1-(0:ℝ))*p.2.2+0*((boundaryCosine K+2*boundaryCosine (K+1))/3)))≠0 := by
      simpa using mul_ne_zero (ne_of_gt (sub_pos.mpr h₁)) (ne_of_gt (sub_pos.mpr h₂))
    exact ((continuousAt_const.div hd hn).add continuousAt_const).prodMk (hlc.prodMk hrc)
  have he : approachGap K p 0=p := by
    simp only [approachGap,sub_zero,zero_mul,add_zero,one_mul]
    simp
  have hh := hc.tendsto
  rw [he] at hh
  exact hh

theorem mem_closure_gapParameterSet {K : ℕ} (hK : 2≤K) {p : ParameterSpace}
    (hp : p∈closedRootTriangle K) (ha : amplitudeFloor p.2.1 p.2.2<p.1) :
    p∈closure (gapParameterSet K) := by
  have ht : Tendsto (fun n : ℕ=>1/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply mem_closure_of_tendsto ((approachGap_tendsto hp hK).comp ht)
  apply Eventually.of_forall
  intro n
  apply approachGap_mem hK hp ha
  · exact one_div_pos.mpr (by positivity)
  · apply (div_le_one (by positivity : 0<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Relative closure in the source's ambient region a>a₀ and r₁>−1. -/
theorem closure_gapParameterSet_iff {K : ℕ} (hK : 2≤K) {p : ParameterSpace}
    (ha : amplitudeFloor p.2.1 p.2.2<p.1) :
    p∈closure (gapParameterSet K) ↔ p∈closedRootTriangle K :=
  ⟨fun hp=>closure_gapParameterSet_subset K hp,fun hp=>mem_closure_gapParameterSet hK hp ha⟩

end polyak.Levels.Chart
