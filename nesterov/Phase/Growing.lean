import nesterov.Phase.SingleAtom

/-!
Article: Lemma `lem:single` (b), persistence of a strict rational phase contact.
Use: continuity gives one strictly growing feasible spectrum, with a strict
minimizer margin and one genuine objective for the whole infinite trajectory.
-/
namespace nesterov.Phase
noncomputable section
open Spectral Set Filter
open scoped Topology

theorem exists_positive_singleton {j K : ℕ} (hcop : j.Coprime K) (hK : 3≤K)
    (a : ℝ→SymbolPair) (c : Frequency) (hω : Real.arccos c=2*Real.pi*j/K)
    (hg : Continuous (fun t=>g (a t) c)) (hs : Continuous (fun t=>skew (a t) c))
    (hne : g (a 0) c≠0 ∨ skew (a 0) c≠0)
    (hphase : |angle (g (a 0) c) (skew (a 0) c)|<Real.pi/K) :
    ∃ t : ℝ,0<t ∧ 0<g (a t) c ∧ Feasible (a t) t (singletonSpectrum c) 0 := by
  have hg0 := phase_small_g_pos hK hne hphase.le
  have hm : Continuous (fun t=>mode (g (a t) c) (skew (a t) c)) := by
    unfold mode
    fun_prop
  have hθ : ContinuousAt (fun t=>angle (g (a t) c) (skew (a t) c)) 0 := by
    apply (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hg0)))).comp
    exact hm.continuousAt
  have hevent : ∀ᶠ t in 𝓝 (0:ℝ),|angle (g (a t) c) (skew (a t) c)|<Real.pi/K ∧ 0<g (a t) c :=
    (hθ.abs.eventually (gt_mem_nhds hphase)).and (hg.continuousAt.eventually (lt_mem_nhds hg0))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  have ht := hball (show dist (δ/2) (0:ℝ)<δ by
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos (by positivity : 0<δ/2)]
    linarith)
  refine ⟨δ/2,by positivity,ht.2,?_⟩
  exact (singleton_feasible_of_phase hcop hK (a (δ/2)) (δ/2) c hω (Or.inl ht.2.ne') ht.1.le).2

/-- The actual polynomial amplitudes have the required joint continuity. -/
theorem exists_growing_singleton (M : StationaryMethod) (μ L : ℝ)
    {j K : ℕ} (hcop : j.Coprime K) (hK : 3≤K) (c : Frequency)
    (hω : Real.arccos c=2*Real.pi*j/K)
    (hne : g (M.symbolPair μ L 0) c≠0 ∨ skew (M.symbolPair μ L 0) c≠0)
    (hphase : |angle (g (M.symbolPair μ L 0) c) (skew (M.symbolPair μ L 0) c)|<Real.pi/K) :
    ∃ t : ℝ,0<t ∧ 0<g (M.symbolPair μ L t) c ∧
      Feasible (M.symbolPair μ L t) t (singletonSpectrum c) 0 := by
  have hu : Continuous (fun t=>(M.symbolPair μ L t).u c) :=
    (M.continuous_symbolPair_u μ L).comp (continuous_id.prodMk continuous_const)
  have hp : Continuous (fun t=>(M.symbolPair μ L t).p c) :=
    (M.continuous_symbolPair_p μ L).comp (continuous_id.prodMk continuous_const)
  apply exists_positive_singleton hcop hK (fun t=>M.symbolPair μ L t) c hω _ _ hne hphase
  · unfold g
    fun_prop
  · unfold skew
    fun_prop

end
end nesterov.Phase
