import nesterov.TwoStep.OneSlowFrequencyNormalization
import Mathlib.Topology.Ultrafilter

/-! Article Proposition 6.3: one slow frequency is not enough. The argument
works for every continuous finite-memory second-order family. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Spectral
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

theorem no_singleProgram_uniform {csharp Γ : ℝ} (_hcs : θ/3<csharp) (hcsQ : csharp<Flow.cQ θ y)
    (hobs : ∀ c γ : ℝ,θ/3<c → c≤csharp → 0≤γ → ¬Flow.OneAtomFeasible θ y c γ)
    (_hΓ : 0<Γ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ c∈Ioc (θ/3) csharp,∀ γ∈Icc (0:ℝ) Γ,∀ C : ℝ,
      ¬SingleProgram ε c γ (F.slowG ε (Slow.SecondOrderFamily.slowPoint c γ))
        (F.slowS ε (Slow.SecondOrderFamily.slowPoint c γ)) C := by
  classical
  by_contra h
  let B : Set ℝ := {ε | ∃ p : ℝ × ℝ × ℝ,p.1∈Ioc (θ/3) csharp ∧ p.2.1∈Icc (0:ℝ) Γ ∧
    SingleProgram ε p.1 p.2.1 (F.slowG ε (Slow.SecondOrderFamily.slowPoint p.1 p.2.1))
      (F.slowS ε (Slow.SecondOrderFamily.slowPoint p.1 p.2.1)) p.2.2}
  have hf : ∃ᶠ ε in 𝓝[>] (0:ℝ),ε∈B := by
    have hh := not_eventually.mp h
    exact hh.mono (fun ε he=>by
      push Not at he
      obtain ⟨c,hc,γ,hγ,C,hp⟩ := he
      exact ⟨(c,γ,C),hc,hγ,hp⟩)
  let L : Filter ℝ := (𝓝[>] (0:ℝ))⊓𝓟 B
  have : NeBot L := frequently_mem_iff_neBot.mp hf
  let p : ℝ→ℝ × ℝ × ℝ := fun ε=>if hε : ε∈B then Classical.choose hε else (0,0,0)
  have hp (ε : ℝ) (hε : ε∈B) : (p ε).1∈Ioc (θ/3) csharp ∧ (p ε).2.1∈Icc (0:ℝ) Γ ∧
      SingleProgram ε (p ε).1 (p ε).2.1 (F.slowG ε (Slow.SecondOrderFamily.slowPoint (p ε).1 (p ε).2.1))
        (F.slowS ε (Slow.SecondOrderFamily.slowPoint (p ε).1 (p ε).2.1)) (p ε).2.2 := by
    simpa only [p,dite_eq_left hε] using Classical.choose_spec hε
  have hB : ∀ᶠ ε in L,ε∈B := (show ∀ᶠ ε in 𝓟 B,ε∈B by simp).filter_mono inf_le_right
  let K := Icc (θ/3) csharp ×ˢ Icc (0:ℝ) Γ
  have hmem : ∀ᶠ ε in L,((p ε).1,(p ε).2.1)∈K := by
    filter_upwards [hB] with ε hε
    exact ⟨⟨(hp ε hε).1.1.le,(hp ε hε).1.2⟩,(hp ε hε).2.1⟩
  obtain ⟨x₀,hx₀,hcluster⟩ := (isCompact_Icc.prod isCompact_Icc).exists_mapClusterPt
    (Filter.tendsto_principal.mpr hmem)
  obtain ⟨U,hUL,hxlim⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hUl : (U:Filter ℝ)≤𝓝[>] (0:ℝ) := hUL.trans inf_le_left
  have heU : Tendsto (fun ε : ℝ=>ε) (U:Filter ℝ) (𝓝[>] (0:ℝ)) := hUl
  have hc := (continuous_fst.tendsto x₀).comp hxlim
  have hγ := (continuous_snd.tendsto x₀).comp hxlim
  have hGU := F.slowG_physical_tendsto heU hc hγ
  have hBU := hB.filter_mono hUL
  have hpU : ∀ᶠ ε in (U:Filter ℝ),SingleProgram ε (p ε).1 (p ε).2.1
      (F.slowG ε (Slow.SecondOrderFamily.slowPoint (p ε).1 (p ε).2.1))
      (F.slowS ε (Slow.SecondOrderFamily.slowPoint (p ε).1 (p ε).2.1)) (p ε).2.2 :=
    hBU.mono (fun ε hε=>(hp ε hε).2.2)
  let R := |x₀.2^2-Flow.delta θ y x₀.1|+1
  have hGbound := hGU.eventually (eventually_lt_nhds
    (show x₀.2^2-Flow.delta θ y x₀.1<R by dsimp [R];linarith [le_abs_self (x₀.2^2-Flow.delta θ y x₀.1)]))
  have hCmem : ∀ᶠ ε in (U:Filter ℝ),(p ε).2.2∈Metric.closedBall (0:ℝ) R := by
    filter_upwards [hpU,hGbound] with ε hpε hb
    rw [mem_closedBall_zero_iff,Real.norm_eq_abs]
    exact hpε.1.trans hb.le
  obtain ⟨C₀,_,hCcluster⟩ := (isCompact_closedBall (0:ℝ) R).exists_mapClusterPt
    (Filter.tendsto_principal.mpr hCmem)
  obtain ⟨V,hVU,hClim⟩ := mapClusterPt_iff_ultrafilter.mp hCcluster
  have heV := heU.mono_left hVU
  have hcV := hc.mono_left hVU
  have hγV := hγ.mono_left hVU
  have hG := F.slowG_physical_tendsto heV hcV hγV
  have hS := F.slowS_physical_tendsto heV hcV hγV
  have hc0 : 0<x₀.1 := by linarith [F.theta_pos,hx₀.1.1]
  have hcQ : x₀.1<Flow.cQ θ y := hx₀.1.2.trans_lt hcsQ
  have hflow := singleProgram_limit_flow heV hcV hγV hClim hc0 hcQ hx₀.2.1 hG hS (hpU.filter_mono hVU)
  by_cases heq : x₀.1=θ/3
  · have hd := (Flow.lt_cQ_iff θ y x₀.1).mp hcQ |>.2
    have hh := hflow.2.2
    have hz : 3*x₀.1-θ=0 := by rw [heq];ring
    rw [hz,zero_mul] at hh
    exact not_le_of_gt (mul_pos hc0 hd) hh
  · exact hobs x₀.1 x₀.2 (lt_of_le_of_ne hx₀.1.1 (Ne.symm heq)) hx₀.1.2 hx₀.2.1 hflow

/-- A single actual atom of slow frequency cannot be feasible in the whole
uniform interval θ/3<c≤csharp, including arbitrary common value charges. -/
theorem no_one_slow_frequency {csharp Γ : ℝ} (hcs : θ/3<csharp) (hcsQ : csharp<Flow.cQ θ y)
    (hobs : ∀ c γ : ℝ,θ/3<c → c≤csharp → 0≤γ → ¬Flow.OneAtomFeasible θ y c γ)
    (hΓ : 0<Γ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ c∈Ioc (θ/3) csharp,∀ γ∈Icc (0:ℝ) Γ,∀ C : ℝ,
      ¬Feasible ((F.method ε).symbolPair (ε^2) 1 (-c*ε)) (-c*ε)
        (Phase.singletonSpectrum (Phase.frequency (ε*γ))) C := by
  have hno := no_singleProgram_uniform F hcs hcsQ hobs hΓ
  have hdef := F.query_band_defined (Ic:=Icc (θ/3) csharp) isCompact_Icc hΓ.le
  have hstep := F.stepAt_tendsto.eventually (eventually_gt_nhds F.step_pos)
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hsmall := he.eventually (eventually_lt_nhds zero_lt_one)
  have hπ := (he.mul_const Γ).eventually (eventually_lt_nhds (by simpa using Real.pi_pos))
  filter_upwards [hno,hdef,hstep,hsmall,hπ,self_mem_nhdsWithin] with ε hε hd hy hε1 hΓπ hε0 c hc γ hγ C hp
  change 0<ε at hε0
  have hω : ε*γ∈Icc (0:ℝ) Real.pi :=
    ⟨mul_nonneg hε0.le hγ.1,(mul_le_mul_of_nonneg_left hγ.2 hε0.le).trans hΓπ.le⟩
  have hU : (F.u ε).eval₂ Complex.ofRealHom (F.wave ε (Slow.SecondOrderFamily.slowPoint c γ))≠0 := by
    have hh := hd c ⟨hc.1.le,hc.2⟩ γ hγ
    rw [F.sampled_query_value hω] at hh
    intro hz
    rw [hz,Complex.normSq_zero] at hh
    norm_num at hh
  obtain ⟨D,hD⟩ := actual_singleton_to_slow F hε0 (by nlinarith) hy hω hU hp
  exact hε c hc γ hγ D hD

/-- Proposition onedisc, with csharp furnished by the proved flow obstruction. -/
theorem exists_one_slow_frequency_exclusion (hgap : θ/3<Flow.cQ θ y) {Γ : ℝ} (hΓ : 0<Γ) :
    ∃ csharp : ℝ,θ/3<csharp ∧ csharp<Flow.cQ θ y ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ c∈Ioc (θ/3) csharp,∀ γ∈Icc (0:ℝ) Γ,∀ C : ℝ,
        ¬Feasible ((F.method ε).symbolPair (ε^2) 1 (-c*ε)) (-c*ε)
          (Phase.singletonSpectrum (Phase.frequency (ε*γ))) C := by
  obtain ⟨csharp,hcs,hcsQ,hobs⟩ := Flow.exists_oneAtom_obstruction F.theta_pos F.step_pos hgap
  exact ⟨csharp,hcs,hcsQ,no_one_slow_frequency F hcs hcsQ hobs hΓ⟩

/-- The exact quantifier order of Proposition onedisc: one common csharp
precedes every frequency-band bound and its positive endpoint neighborhood. -/
theorem one_slow_frequency_is_not_enough (hgap : θ/3<Flow.cQ θ y) :
    ∃ csharp : ℝ,θ/3<csharp ∧ csharp<Flow.cQ θ y ∧
      ∀ Γ : ℝ,0<Γ → ∃ ε₁ : ℝ,0<ε₁ ∧ ∀ ε∈Ioo (0:ℝ) ε₁,
        ∀ c∈Ioc (θ/3) csharp,∀ γ∈Icc (0:ℝ) Γ,∀ C : ℝ,
          ¬Feasible ((F.method ε).symbolPair (ε^2) 1 (-c*ε)) (-c*ε)
            (Phase.singletonSpectrum (Phase.frequency (ε*γ))) C := by
  obtain ⟨csharp,hcs,hcsQ,hobs⟩ := Flow.exists_oneAtom_obstruction F.theta_pos F.step_pos hgap
  refine ⟨csharp,hcs,hcsQ,fun Γ hΓ=>?_⟩
  obtain ⟨ε₁,hε₁,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (no_one_slow_frequency F hcs hcsQ hobs hΓ)
  exact ⟨ε₁,hε₁,fun ε hε=>hsub hε⟩

end
end nesterov.TwoStep
