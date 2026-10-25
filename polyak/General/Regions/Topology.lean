import polyak.General.Regions.Explicit

/-! Article: Theorem A(iii). All topological statements use the admissible
parameter domain itself, hence its relative topology rather than the ambient
closed half-space beta>=0. -/
namespace polyak.General
noncomputable section
open Filter
open scoped Topology

instance : TopologicalSpace Tuning := TopologicalSpace.induced
  (fun q : Tuning => (q.kappa,q.y,q.beta)) inferInstance

namespace Tuning

@[fun_prop] theorem continuous_coordinates : Continuous (fun q : Tuning => (q.kappa,q.y,q.beta)) :=
  continuous_induced_dom

@[fun_prop] theorem continuous_kappa : Continuous Tuning.kappa :=
  continuous_fst.comp continuous_coordinates

@[fun_prop] theorem continuous_y : Continuous Tuning.y :=
  (continuous_fst.comp continuous_snd).comp continuous_coordinates

@[fun_prop] theorem continuous_beta : Continuous Tuning.beta :=
  (continuous_snd.comp continuous_snd).comp continuous_coordinates

@[fun_prop] theorem continuous_x : Continuous Tuning.x := by
  exact continuous_y.div continuous_kappa (fun q => ne_of_gt q.kappa_pos)

@[fun_prop] theorem continuous_L (c : ℝ) : Continuous (fun q : Tuning => q.L c) := by
  unfold L
  fun_prop

end Tuning
namespace Regions

/-- Strict lag-one positivity is open in the relative tuning domain. -/
theorem isOpen_omegaOne : IsOpen {q : Tuning | OmegaOne q} := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hcont : Continuous (fun p : Tuning×ℝ=>p.1.L p.2) := by
    unfold Tuning.L
    fun_prop
  have hlocal (c : ℝ) (hc : c∈Set.Icc (-1:ℝ) 1) :
      ∀ᶠ p : Tuning×ℝ in 𝓝 (q,c),0<p.1.L p.2 :=
    hcont.continuousAt.eventually (eventually_gt_nhds (hq c hc))
  exact isCompact_Icc.eventually_forall_of_forall_eventually hlocal

/-- The weak closed lag-one region; distinct from OmegaOne at tangencies. -/
def WeakOmegaOne (q : Tuning) : Prop := ∀ c∈Set.Icc (-1:ℝ) 1,0≤q.L c

/-- Every point in the relative closure has a globally nonnegative lag-one symbol. -/
theorem closure_omegaOne_subset_weak : closure {q : Tuning | OmegaOne q} ⊆
    {q : Tuning | WeakOmegaOne q} := by
  intro q hq c hc
  have hclosed : IsClosed {p : Tuning | 0≤p.L c} :=
    isClosed_le continuous_const (Tuning.continuous_L c)
  exact (hclosed.closure_subset_iff.mpr (fun p hp => (hp c hc).le)) hq

/-- At a weak boundary zero, the chosen cosine is an actual zero of the cubic. -/
theorem weak_zero_cubic {q : Tuning} (hq : WeakOmegaOne q) {c : ℝ}
    (hc : c∈Set.Icc (-1:ℝ) 1) (hz : q.L c≤0) : q.H 1 c=0 := by
  have h : q.L c=0 := le_antisymm hz (hq c hc)
  rw [q.H_one,h,mul_zero]

/-- Every relative boundary point is weakly feasible and has an interior zero. -/
theorem frontier_omegaOne_has_zero {q : Tuning}
    (hq : q∈frontier {p : Tuning | OmegaOne p}) :
    WeakOmegaOne q ∧ ∃ c∈Set.Ioo (-1:ℝ) 1,q.L c=0 := by
  have hw := closure_omegaOne_subset_weak (frontier_subset_closure hq)
  refine ⟨hw,?_⟩
  have hn : ¬OmegaOne q := by
    rw [isOpen_omegaOne.frontier_eq] at hq
    exact hq.2
  unfold OmegaOne at hn
  push Not at hn
  obtain ⟨c,hc,hval⟩ := hn
  have he : q.L c=0 := le_antisymm hval (hw c hc)
  have hcl : -1<c := lt_of_le_of_ne hc.1 (fun hh=>by subst c; linarith [q.L_neg_one_pos])
  have hcr : c<1 := lt_of_le_of_ne hc.2 (fun hh=>by subst c; linarith [q.L_one_pos])
  exact ⟨c,⟨hcl,hcr⟩,he⟩

end Regions
end
end polyak.General
