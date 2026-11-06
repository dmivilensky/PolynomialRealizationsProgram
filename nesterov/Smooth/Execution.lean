import nesterov.Stationary.Execution
import nesterov.Smooth.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: Remark `rem:uniform-smoothness`, Appendix A.
Use: exact causal trajectories with a fixed initial memory vary continuously
under a uniform approximation of the gradient. This preserves from-rest data.
-/
namespace nesterov.Smooth
noncomputable section
open Filter
open scoped Topology BigOperators ContDiff

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform gradient error and fixed initial memory imply convergence of every
actual finite execution prefix. The same initial memory is used throughout. -/
theorem run_tendsto (M : StationaryMethod) {ι : Type*} {l : Filter ι}
    {g : E → E} (hg : Continuous g) {a : ι → E → E} {err : ι → ℝ}
    (he : Tendsto err l (𝓝 0)) (ha : ∀ i x, ‖a i x-g x‖ ≤ err i)
    (initial : Fin M.memory → E) (n : ℕ) :
    Tendsto (fun i => M.run (a i) initial n) l (𝓝 (M.run g initial n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<M.memory
    · have hi i : M.run (a i) initial n=initial ⟨n,hn⟩ := M.run_initial _ _ ⟨n,hn⟩
      simpa only [hi,M.run_initial g initial ⟨n,hn⟩] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => initial ⟨n,hn⟩) l (𝓝 (initial ⟨n,hn⟩)))
    · let k := n-M.memory
      have heq : n=k+M.memory := by dsimp [k]; omega
      have hq : Tendsto (fun i => M.query (M.run (a i) initial) k) l
          (𝓝 (M.query (M.run g initial) k)) := by
        unfold StationaryMethod.query
        apply tendsto_finsetSum
        intro j _
        exact tendsto_const_nhds.smul (ih (k+j) (by dsimp [k]; omega))
      have herror : Tendsto
          (fun i => a i (M.query (M.run (a i) initial) k)-
            g (M.query (M.run (a i) initial) k)) l (𝓝 0) :=
        squeeze_zero_norm (fun i => ha i _) he
      have hgrad : Tendsto (fun i => a i (M.query (M.run (a i) initial) k)) l
          (𝓝 (g (M.query (M.run g initial) k))) := by
        convert herror.add ((hg.tendsto _).comp hq) using 1 <;> simp
      have hsum : Tendsto
          (fun i => ∑ j : Fin M.memory, M.recurrenceCoeff j.castSucc • M.run (a i) initial (k+j)) l
          (𝓝 (∑ j : Fin M.memory, M.recurrenceCoeff j.castSucc • M.run g initial (k+j))) := by
        apply tendsto_finsetSum
        intro j _
        exact tendsto_const_nhds.smul (ih (k+j) (by dsimp [k]; omega))
      have hlast := (tendsto_const_nhds
        (x := (M.recurrenceCoeff (Fin.last M.memory))⁻¹) (f := l)).smul (hgrad.sub hsum)
      simpa only [heq,M.run_step] using hlast

omit [NormedSpace ℝ E] in
/-- The complete Hilbert memory-state norm also converges at every fixed time. -/
theorem stateNorm_tendsto (M : StationaryMethod) {ι : Type*} {l : Filter ι}
    {w : ι → ℕ → E} {v : ℕ → E} (hw : ∀ n, Tendsto (fun i => w i n) l (𝓝 (v n)))
    (k : ℕ) : Tendsto (fun i => M.stateNorm (w i) k) l (𝓝 (M.stateNorm v k)) := by
  unfold StationaryMethod.stateNorm
  apply Tendsto.sqrt
  apply tendsto_finsetSum
  intro j _
  exact (hw (k+j)).norm.pow 2


end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A concrete sequence of centered C∞ objectives, all with the exact same
curvature constants, approximates every fixed execution prefix. -/
theorem exists_smooth_runs (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
    (M : StationaryMethod) {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) (initial : Fin M.memory → E) :
    ∃ fs : ℕ → E → ℝ,
      (∀ i, polyak.CenteredSmoothStronglyConvex μ L (fs i) ∧ ContDiff ℝ ∞ (fs i)) ∧
      (∀ x i, ‖gradient (fs i) x-gradient f x‖ ≤ ((i:ℝ)+1)⁻¹) ∧
      (∀ n, Tendsto (fun i => M.run (gradient (fs i)) initial n) atTop
        (𝓝 (M.run (gradient f) initial n))) := by
  have hex (i : ℕ) := exists_centered_contDiff_approx m hf
    (show 0 < ((i:ℝ)+1)⁻¹ by positivity)
  choose fs hc hs he using hex
  refine ⟨fs,fun i => ⟨hc i,hs i⟩,fun x i => (he i x).le,?_⟩
  intro n
  have hg : Continuous (gradient f) := by
    have hL : 0 ≤ L := by linarith [hf.mu_pos,hf.mu_lt_L]
    have h : LipschitzWith (Real.toNNReal L) (gradient f) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm,Real.coe_toNNReal L hL] using hf.grad_lipschitz x y
    exact h.continuous
  apply run_tendsto M hg (err := fun i : ℕ => ((i:ℝ)+1)⁻¹)
  · have hz : Tendsto (fun i : ℕ => (1:ℝ)/((i:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [one_div] using hz
  · exact fun i x => (he i x).le

end
end nesterov.Smooth
