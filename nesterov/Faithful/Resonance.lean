import nesterov.Faithful.Algebra
import nesterov.Phase.Growing

/-!
Article: Theorem faithful(d), the continuity-and-realization part.
Use: a strict rational phase contact persists under coefficient limits and
produces one genuine planar objective for all times, without stability.
-/
namespace nesterov.Faithful
noncomputable section
open Spectral Phase Filter Set
open scoped Topology NNReal

/-- Strict phase locking gives a growing actual real planar trajectory. -/
theorem growing_planar_of_phase (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L)
    {j K : ℕ} (hcop : j.Coprime K) (hK : 3≤K) (c : Frequency)
    (hω : Real.arccos c=2*Real.pi*j/K)
    (hne : g (M.symbolPair μ L 0) c≠0 ∨ skew (M.symbolPair μ L 0) c≠0)
    (hphase : |angle (g (M.symbolPair μ L 0) c) (skew (M.symbolPair μ L 0) c)|<Real.pi/K) :
    ∃ t : ℝ,0<t ∧ Feasible (M.symbolPair μ L t) t (singletonSpectrum c) 0 ∧
      1<Rates.rate M μ L ∧
      ∃ (f : EuclideanSpace ℝ (Fin 2)→ℝ) (x : ℕ→EuclideanSpace ℝ (Fin 2)),
        polyak.CenteredSmoothStronglyConvex μ L f ∧ M.IsTrajectory (gradient f) x ∧
        (∀ k : ℕ,‖x k‖=Real.exp (k*t)) := by
  obtain ⟨t,ht,_,hf⟩ := exists_growing_singleton M μ L hcop hK c hω hne hphase
  refine ⟨t,ht,hf,?_,?_⟩
  · exact (show (1:ℝ)<Real.exp t by simpa using Real.exp_lt_exp.mpr ht).trans_le (hf.exp_le_rate hμ hμL)
  · have hr := finite_exists_real_objective M hμ hμL (fun _ : Fin 1=>(1:ℝ≥0))
      (fun _=>c) (by simp) hf
    have hd : 2*Fintype.card (Fin 1)=2 := by norm_num
    rw [hd] at hr
    exact hr

/-- The branch is continuous at a strict contact, since its real part is
positive.  Only convergence of the two spectral coordinates is required. -/
theorem eventually_strict_phase {α : Type*} {l : Filter α}
    {K : ℕ} (hK : 3≤K) (a : α→SymbolPair) (a₀ : SymbolPair) (c : Frequency)
    (hg : Tendsto (fun e=>g (a e) c) l (𝓝 (g a₀ c)))
    (hs : Tendsto (fun e=>skew (a e) c) l (𝓝 (skew a₀ c)))
    (hne : g a₀ c≠0 ∨ skew a₀ c≠0)
    (hphase : |angle (g a₀ c) (skew a₀ c)|<Real.pi/K) :
    ∀ᶠ e in l,0<g (a e) c ∧
      |angle (g (a e) c) (skew (a e) c)|<Real.pi/K := by
  have hg₀ := phase_small_g_pos hK hne hphase.le
  have hm : Tendsto (fun e=>mode (g (a e) c) (skew (a e) c)) l
      (𝓝 (mode (g a₀ c) (skew a₀ c))) := by
    unfold mode
    exact hg.ofReal.add (tendsto_const_nhds.mul hs.ofReal)
  have harg : ContinuousAt Complex.arg (mode (g a₀ c) (skew a₀ c)) :=
    Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hg₀)))
  have ha := harg.tendsto.comp hm
  exact (hg.eventually (lt_mem_nhds hg₀)).and (ha.abs.eventually (gt_mem_nhds hphase))

end
end nesterov.Faithful
