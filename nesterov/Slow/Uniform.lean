import nesterov.Slow.QueryLimits
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Uniform compact slow-mode limits follow from the proved moving-mode limits. -/
namespace nesterov.Slow
noncomputable section
open Filter Set Polynomial
open scoped Topology Uniformity

/-- A joint endpoint limit gives uniform convergence on every compact parameter set. -/
lemma uniform_on_compact_of_joint_limit {A B C : Type*} [TopologicalSpace B] [UniformSpace C]
    {l : Filter A} {F : A→B→C} {f : B→C} (hf : Continuous f)
    (h : ∀ b : B,Tendsto (fun p : A × B=>F p.1 p.2) (l ×ˢ 𝓝 b) (𝓝 (f b)))
    {K : Set B} (hK : IsCompact K) : TendstoUniformlyOn F f l K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro b _
  have hb : Tendsto (Prod.snd : A × B→B) (l ×ˢ 𝓝[K] b) (𝓝 b) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hF : Tendsto (fun p : A × B=>F p.1 p.2) (l ×ˢ 𝓝[K] b) (𝓝 (f b)) :=
    (h b).mono_left (prod_mono_right l (nhdsWithin_le_nhds : 𝓝[K] b≤𝓝 b))
  exact (((hf.tendsto b).comp hb).prodMk_nhds hF).mono_right (nhds_le_uniformity _)


lemma uniformly_eventually_norm_bounded {A B C : Type*} [TopologicalSpace B]
    [NormedAddCommGroup C] {l : Filter A} {F : A→B→C} {f : B→C}
    {K : Set B} (hK : IsCompact K) (hf : Continuous f)
    (h : TendstoUniformlyOn F f l K) :
    ∃ R : ℝ,0<R ∧ ∀ᶠ a in l,∀ b∈K,‖F a b‖≤R := by
  obtain ⟨R,hR⟩ := (hK.image hf).isBounded.exists_norm_le
  have hh := Metric.tendstoUniformlyOn_iff.mp h 1 zero_lt_one
  refine ⟨|R|+2,by positivity,?_⟩
  filter_upwards [hh] with a ha b hb
  have hfb := hR (f b) ⟨b,hb,rfl⟩
  have hdiff : ‖F a b-f b‖≤1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using (ha b hb).le
  calc
    ‖F a b‖=‖(F a b-f b)+f b‖ := by rw [sub_add_cancel]
    _≤‖F a b-f b‖+‖f b‖ := norm_add_le _ _
    _≤1+R := add_le_add hdiff hfb
    _≤|R|+2 := by linarith [le_abs_self R]

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

theorem query_wave_uniform {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun ε w=>(F.u ε).eval₂ Complex.ofRealHom (F.wave ε w))
      (fun _=>(1:ℂ)) (𝓝[>] (0:ℝ)) K := by
  apply uniform_on_compact_of_joint_limit continuous_const _ hK
  intro w
  exact F.query_wave_tendsto tendsto_fst tendsto_snd

theorem scaledCurvature_uniform {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn F.scaledCurvature (fun w=>w*((θ:ℂ)-w)/(y:ℂ)) (𝓝[>] (0:ℝ)) K := by
  apply uniform_on_compact_of_joint_limit (by fun_prop) _ hK
  intro w
  exact F.scaledCurvature_tendsto tendsto_fst tendsto_snd

set_option maxHeartbeats 0 in
theorem slowG_uniform {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun ε p=>F.slowG ε (slowPoint p.1 p.2))
      (fun p=>p.2^2-nesterov.Flow.delta θ y p.1) (𝓝[>] (0:ℝ)) K := by
  apply uniform_on_compact_of_joint_limit (by unfold nesterov.Flow.delta;fun_prop) _ hK
  intro p
  have he : Tendsto (Prod.fst : ℝ × (ℝ × ℝ)→ℝ) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 p) (𝓝[>] (0:ℝ)) := tendsto_fst
  have hp : Tendsto (Prod.snd : ℝ × (ℝ × ℝ)→ℝ × ℝ) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 p) (𝓝 p) := tendsto_snd
  exact F.slowG_physical_tendsto he ((continuous_fst.tendsto p).comp hp) ((continuous_snd.tendsto p).comp hp)

set_option maxHeartbeats 0 in
theorem slowS_uniform {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun ε p=>F.slowS ε (slowPoint p.1 p.2))
      (fun p=>(θ-2*p.1)*p.2) (𝓝[>] (0:ℝ)) K := by
  apply uniform_on_compact_of_joint_limit (by fun_prop) _ hK
  intro p
  have he : Tendsto (Prod.fst : ℝ × (ℝ × ℝ)→ℝ) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 p) (𝓝[>] (0:ℝ)) := tendsto_fst
  have hp : Tendsto (Prod.snd : ℝ × (ℝ × ℝ)→ℝ × ℝ) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 p) (𝓝 p) := tendsto_snd
  exact F.slowS_physical_tendsto he ((continuous_fst.tendsto p).comp hp) ((continuous_snd.tendsto p).comp hp)


/-- One bound works on the full compact parameter set before ε is chosen. -/
theorem slow_coefficients_uniform_bound {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ p∈K,
      |F.slowG ε (slowPoint p.1 p.2)|≤B ∧ |F.slowS ε (slowPoint p.1 p.2)|≤B := by
  obtain ⟨B₁,hB₁,h₁⟩ := uniformly_eventually_norm_bounded hK
    (by unfold nesterov.Flow.delta;fun_prop) (F.slowG_uniform hK)
  obtain ⟨B₂,hB₂,h₂⟩ := uniformly_eventually_norm_bounded hK (by fun_prop) (F.slowS_uniform hK)
  refine ⟨max B₁ B₂,lt_max_of_lt_left hB₁,?_⟩
  filter_upwards [h₁,h₂] with ε hε₁ hε₂ p hp
  exact ⟨(hε₁ p hp).trans (le_max_left _ _),(hε₂ p hp).trans (le_max_right _ _)⟩


/-- Uniform O(ε²) bounds for both actual query-normalized spectral coefficients. -/
theorem query_coefficients_uniform_bound {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ p∈K,
      |1-Complex.normSq (F.queryRatio ε (slowPoint p.1 p.2))|≤B*ε^2 ∧
      |2*(F.queryRatio ε (slowPoint p.1 p.2)).im|≤B*ε^2 := by
  obtain ⟨B,hB,hbound⟩ := F.slow_coefficients_uniform_bound hK
  have hyp : 0<y := F.step_pos
  have hy : 0<y/2 := by linarith [F.step_pos]
  have hstep := F.stepAt_tendsto.eventually (eventually_gt_nhds (show y/2<y by linarith [F.step_pos]))
  refine ⟨8*B/y,by positivity,?_⟩
  filter_upwards [hbound,hstep,self_mem_nhdsWithin,
    (show ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 from
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds)]
    with ε hε hs hp hsmall p hKp
  change 0<ε at hp
  have hs0 : 0<F.stepAt ε := hy.trans hs
  have he1 : ε^2≠1 := by nlinarith
  have he := F.query_coefficients_exact hp.ne' he1 hs0.ne' (slowPoint p.1 p.2)
  have hscale : 0≤4*ε^2/F.stepAt ε := by positivity
  have hrec : 4*ε^2/F.stepAt ε≤8*ε^2/y := by
    have hh := div_le_div_of_nonneg_left (show 0≤4*ε^2 by positivity) hy hs.le
    convert hh using 1
    field_simp
    ring
  have hGb := mul_le_mul_of_nonneg_left (hε p hKp).1 hscale
  have hSb := mul_le_mul_of_nonneg_left (hε p hKp).2 hscale
  rw [←abs_of_nonneg hscale,←abs_mul,←he.1] at hGb
  rw [←abs_of_nonneg hscale,←abs_mul,←he.2] at hSb
  rw [abs_of_nonneg hscale] at hGb hSb
  have ht : (4*ε^2/F.stepAt ε)*B≤(8*B/y)*ε^2 := by
    have hh := mul_le_mul_of_nonneg_right hrec hB.le
    convert hh using 1
    ring
  exact ⟨hGb.trans ht,hSb.trans ht⟩

end SecondOrderFamily
end
end nesterov.Slow
