import krylov.Convergence.ObservableRFCWindow
import krylov.Convergence.ObservableSemantics

/-!
Article: main_krylov, apG:Dunif, true observable RFC state invariant.
Use: maintain source localization, actual measured pair control and the
genuine projected gradient through the literal real cycle. The invariant
is proved along execution; it is never an input to the source theorem.
Source: actual newest-first observations and finite normalized geometry.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual canonical primal stored steps, with no reference transcript.
Article: main_krylov, apG:Dunif. -/
def observablePrimal (T : E ≃L[ℝ] E) (B : History E) : Fin B.pairs.length → E :=
  fun i=>T (windowSteps B.pairs i)

/-- Actual canonical dual measured gradient differences.
Article: main_krylov, apG:Dunif. -/
def observableDual (T : E ≃L[ℝ] E) (B : History E) : Fin B.pairs.length → E :=
  fun i=>T.symm (windowImages B.pairs i)

/-- Absolute uniform projected-gradient allowance along a real RFC
cycle. Its dimension dependence is exactly n^(3/2).
Article: main_krylov, apG:Dunif. -/
def observableRFCResidualBudget (N : ℕ) (epsilon e : ℝ) : ℝ :=
  2048*(N:ℝ)*Real.sqrt N*epsilon^2*e

/-- Analytic invariant of actual observed states. Every field concerns
the genuine current point, true function values and real stored pairs.
Article: main_krylov, apG:Dunif. -/
structure ObservableRFCInvariant (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (x₀ : E) (N : ℕ) (epsilon bar : ℝ) (B : History E) : Prop where
  gradient : B.gradient=G (x₀+B.displacement)
  point : ‖T (x₀+B.displacement)‖≤2*‖T x₀‖
  value : f (x₀+B.displacement)≤f x₀
  steps : ∀ i,observablePrimal T B i≠0
  pairs : ∀ i,‖observableDual T B i-observablePrimal T B i‖≤
    (2*epsilon)*‖observablePrimal T B i‖
  angles : ∀ i j,i≠j → |inner ℝ (unitWindow (observablePrimal T B) i)
    (unitWindow (observablePrimal T B) j)|≤2*epsilon+3*bar
  residual : ‖projectedResidual (unitWindow (observablePrimal T B)) (T.symm B.gradient)‖≤
    observableRFCResidualBudget N epsilon ‖T x₀‖

/-- The actual fresh cycle satisfies the full analytic invariant before
any search, with a genuine zero empty-span projected residual.
Article: main_krylov, apG:Dunif. -/
theorem observable_rfc_initial_invariant (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (x₀ : E) (N : ℕ) (epsilon bar : ℝ) :
    ObservableRFCInvariant T f G x₀ N epsilon bar ⟨G x₀,[]⟩ := by
  refine ⟨by simp only [History.gradient,History.displacement,List.map_nil,List.sum_nil,add_zero],
    ?_,by simp only [History.displacement,List.map_nil,List.sum_nil,add_zero,le_refl],
    (fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i),?_⟩
  · simp only [History.displacement,List.map_nil,List.sum_nil,add_zero]
    nlinarith only [norm_nonneg (T x₀)]
  · have hz : projectedResidual (unitWindow (observablePrimal T (History.mk (G x₀) [])))
        (T.symm (History.mk (G x₀) []).gradient)=0 := by
      ext i
      exact Fin.elim0 i
    rw [hz,norm_zero]
    dsimp only [observableRFCResidualBudget]
    positivity

/-- The true measured normalized skew defect is invariant under the
original primal/dual metric transformation.
Article: main_krylov, apG:Dunif, actual defect test dictionary. -/
theorem observable_metric_pairDefect {p : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y : Fin p → E) :
    pairDefect (fun i=>T (s i)) (fun i=>T.symm (y i))=pairDefect s y := by
  ext i j
  simp only [pairDefect,metric_primal_dual_pairing T hT]

/-- The invariant derives the actually implemented old solve domain,
actual defect norm, normalized conditioning and exact spectral margin.
Article: main_krylov, apG:Dunif, no independent inverse assumptions. -/
theorem ObservableRFCInvariant.domains {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {x₀ : E} {N : ℕ} {epsilon bar : ℝ} {B : History E}
    (I : ObservableRFCInvariant T f G x₀ N epsilon bar B)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (hn : 1≤N) (hsize : B.records.length≤N) (he : 0≤epsilon) (hb : 0≤bar)
    (hsmall : (N:ℝ)*epsilon≤1/128) (hbar : (N:ℝ)*bar≤1/16) :
    IsUnit (crossGram (windowImages (selectedWindow fullMemory B))
      (windowSteps (selectedWindow fullMemory B))).det ∧
    ‖windowDefect (selectedWindow fullMemory B)‖<1 ∧
    ‖crossGram (unitWindow (observablePrimal T B)) (unitWindow (observablePrimal T B))-1‖≤1/4 ∧
    (∀ i,(3/4:ℝ)≤(crossGram_isHermitian (unitWindow (observablePrimal T B))).eigenvalues i) := by
  have hdim : B.pairs.length≤N := by rw [History.pairs_length];exact hsize
  have h := observable_rfc_window_domains (observablePrimal T B) (observableDual T B) I.steps
    N epsilon bar hn hdim he hb hsmall hbar I.pairs I.angles
  have hC := h.2.2.1
  change IsUnit (crossGram (fun i=>T.symm (windowImages B.pairs i))
    (fun i=>T (windowSteps B.pairs i))).det at hC
  rw [observable_metric_crossGram T hT] at hC
  have hdef := h.2.2.2.2.1
  change ‖pairDefect (fun i=>T (windowSteps B.pairs i))
    (fun i=>T.symm (windowImages B.pairs i))‖<1 at hdef
  rw [observable_metric_pairDefect T hT] at hdef
  rw [selectedWindow_full]
  exact ⟨hC,hdef,h.1,h.2.2.2.2.2⟩

/-- Every actually computed old FC direction annihilates all genuine
dual stored images once the derived true solve domain is available.
Article: main_krylov, apG:Dunif. -/
theorem observable_direction_conjugate (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (B : History E)
    (hC : IsUnit (crossGram (windowImages (selectedWindow fullMemory B))
      (windowSteps (selectedWindow fullMemory B))).det) (i : Fin B.pairs.length) :
    inner ℝ (observableDual T B i) (T (rfcFunctionDirection fullMemory B))=0 := by
  rw [selectedWindow_full] at hC
  have hh := congrFun (conjugacyDirection_conjugate (windowSteps B.pairs) (windowImages B.pairs) B.gradient hC) i
  change inner ℝ (windowImages B.pairs i) (windowDirection B.pairs B.gradient)=0 at hh
  change inner ℝ (T.symm (windowImages B.pairs i)) (T (rfcFunctionDirection fullMemory B))=0
  rw [real_inner_comm,metric_primal_dual_pairing T hT,real_inner_comm]
  simpa only [rfcFunctionDirection,selectedWindow_full] using hh

end
end krylov.Convergence
