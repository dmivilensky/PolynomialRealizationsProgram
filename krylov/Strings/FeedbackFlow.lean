import krylov.Strings.FeedbackAlgebra
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FunProp

/-!
Article: main_krylov, thm:value, uniqueness and feedback construction.
Use: build the local physical feedback state with the existing Picard–Lindelöf
theorem. The graph function is an explicit input here; constructing the global
separatrix and its analytic regularity remains the independent orbit theorem.
Source: Mathlib.Analysis.ODE.ExistUnique, local C¹ vector fields.
-/

namespace krylov.Strings
noncomputable section
open Set
open Filter Topology

/-- Physical state (φ,p,K), with its ordinary product Banach-space structure. -/
abbrev FeedbackState := ℝ × ℝ × ℝ

/-- Closed-loop physical vector field in the proof of uniqueness. -/
def feedbackField (σ : ℝ → ℝ) (z : FeedbackState) : FeedbackState :=
  (z.2.1, z.2.1 ^ 2 / (z.1 * σ (stateRatio z.1 z.2.1 z.2.2)),
    z.2.1 ^ 2 / σ (stateRatio z.1 z.2.1 z.2.2))

/-- The actual feedback field is C¹ wherever the graph is C¹ and its
physical denominators do not vanish. -/
theorem feedbackField_contDiffAt {σ : ℝ → ℝ} {z : FeedbackState}
    (hσ : ContDiffAt ℝ 1 σ (stateRatio z.1 z.2.1 z.2.2))
    (hφ : z.1 ≠ 0) (hK : z.2.2 ≠ 0)
    (hσn : σ (stateRatio z.1 z.2.1 z.2.2) ≠ 0) :
    ContDiffAt ℝ 1 (feedbackField σ) z := by
  have hr : ContDiffAt ℝ 1
      (fun w : FeedbackState ↦ stateRatio w.1 w.2.1 w.2.2) z := by
    dsimp [stateRatio]
    fun_prop
  have hc := hσ.comp z hr
  have hd : z.1 * σ (stateRatio z.1 z.2.1 z.2.2) ≠ 0 := mul_ne_zero hφ hσn
  change ContDiffAt ℝ 1
    (fun w : FeedbackState ↦ (w.2.1,
      w.2.1 ^ 2 / (w.1 * σ (stateRatio w.1 w.2.1 w.2.2)),
      w.2.1 ^ 2 / σ (stateRatio w.1 w.2.1 w.2.2))) z
  fun_prop

/-- A genuine local solution of the physical feedback ODE, initialized
at the source's unit state. This is an existence conclusion, not a supplied
solution field in an abstract optimizer structure. -/
theorem feedback_local_solution {σ : ℝ → ℝ}
    (hσ : ContDiffAt ℝ 1 σ 1) (hσn : σ 1 ≠ 0) :
    ∃ α : ℝ → FeedbackState, α 0 = (1, 1, 1) ∧ ∃ ε > (0 : ℝ),
      ∀ x ∈ Ioo (-ε) ε, HasDerivAt α (feedbackField σ (α x)) x := by
  have hf : ContDiffAt ℝ 1 (feedbackField σ) (1, 1, 1) :=
    feedbackField_contDiffAt (by simpa [stateRatio] using hσ) (by norm_num)
      (by norm_num) (by simpa [stateRatio] using hσn)
  simpa using hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0

/-- The actual local solution can be chosen inside the positive physical
state domain, with positive feedback graph. No global orbit claim is used. -/
theorem feedback_local_positive_solution {σ : ℝ → ℝ}
    (hσ : ContDiffAt ℝ 1 σ 1) (hσpos : 0 < σ 1) :
    ∃ α : ℝ → FeedbackState, α 0 = (1, 1, 1) ∧ ∃ ε > (0 : ℝ),
      ∀ x ∈ Ioo (-ε) ε,
        HasDerivAt α (feedbackField σ (α x)) x ∧
        0 < (α x).1 ∧ 0 < (α x).2.1 ∧ 0 < (α x).2.2 ∧
        0 < σ (stateRatio (α x).1 (α x).2.1 (α x).2.2) := by
  obtain ⟨α, hα₀, ε, hε, hα⟩ := feedback_local_solution hσ hσpos.ne'
  have hc := (hα 0 (by constructor <;> linarith)).continuousAt
  have hφ₀ : (α 0).1 ≠ 0 := by simp [hα₀]
  have hK₀ : (α 0).2.2 ≠ 0 := by simp [hα₀]
  have hr : ContinuousAt (fun x ↦ stateRatio (α x).1 (α x).2.1 (α x).2.2) 0 := by
    dsimp [stateRatio]
    fun_prop
  have hσc : ContinuousAt σ (stateRatio (α 0).1 (α 0).2.1 (α 0).2.2) := by
    simpa [hα₀, stateRatio] using hσ.continuousAt
  have hpos : ∀ᶠ x in 𝓝 (0 : ℝ),
      0 < (α x).1 ∧ 0 < (α x).2.1 ∧ 0 < (α x).2.2 ∧
        0 < σ (stateRatio (α x).1 (α x).2.1 (α x).2.2) := by
    exact (hc.fst.tendsto.eventually (lt_mem_nhds (by simp [hα₀]))).and
      ((hc.snd.fst.tendsto.eventually (lt_mem_nhds (by simp [hα₀]))).and
      ((hc.snd.snd.tendsto.eventually (lt_mem_nhds (by simp [hα₀]))).and
      ((hσc.tendsto.comp hr.tendsto).eventually (lt_mem_nhds (by simpa [hα₀, stateRatio] using hσpos)))))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hpos
  refine ⟨α, hα₀, min ε δ, lt_min hε hδ, ?_⟩
  intro x hx
  have hxe : x ∈ Ioo (-ε) ε := by
    constructor
    · linarith [hx.1, min_le_left ε δ]
    · exact hx.2.trans_le (min_le_left ε δ)
  have hxd : x ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [hx.1, min_le_right ε δ],
      hx.2.trans_le (min_le_right ε δ)⟩
  exact ⟨hα x hxe, hball x hxd⟩

/-- Local uniqueness follows from the derived C¹ field, not an assumed
Lipschitz constant or an axiom of an optimizer object. -/
theorem feedback_local_unique {σ : ℝ → ℝ} {z : FeedbackState}
    (hσ : ContDiffAt ℝ 1 σ (stateRatio z.1 z.2.1 z.2.2))
    (hφ : z.1 ≠ 0) (hK : z.2.2 ≠ 0)
    (hσn : σ (stateRatio z.1 z.2.1 z.2.2) ≠ 0)
    {α β : ℝ → FeedbackState} {x₀ : ℝ}
    (hα₀ : α x₀ = z) (hβ₀ : β x₀ = z)
    (hα : ∀ᶠ x in 𝓝 x₀, HasDerivAt α (feedbackField σ (α x)) x)
    (hβ : ∀ᶠ x in 𝓝 x₀, HasDerivAt β (feedbackField σ (β x)) x) :
    α =ᶠ[𝓝 x₀] β := by
  obtain ⟨C, S, hS, hl⟩ :=
    (feedbackField_contDiffAt hσ hφ hK hσn).exists_lipschitzOnWith
  have hαS : ∀ᶠ x in 𝓝 x₀, α x ∈ S := by
    apply (hα.self_of_nhds.continuousAt.tendsto).eventually
    simpa [hα₀] using hS
  have hβS : ∀ᶠ x in 𝓝 x₀, β x ∈ S := by
    apply (hβ.self_of_nhds.continuousAt.tendsto).eventually
    simpa [hβ₀] using hS
  exact ODE_solution_unique_of_eventually (v := fun _ ↦ feedbackField σ)
    (s := fun _ ↦ S) (K := C) (Eventually.of_forall fun _ ↦ hl)
    (hα.and hαS) (hβ.and hβS) (hα₀.trans hβ₀.symm)

end
end krylov.Strings
