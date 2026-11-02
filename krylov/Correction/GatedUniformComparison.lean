import krylov.Correction.ModelThreshold
import krylov.Correction.GatedDefinedComparison

/-!
Article: main_krylov, thm:UCg(iii), true uniform arbitrary-threshold comparison.
Use: Prove that every actually defined nonstagnating gated cycle is exactly
the original ordinary RFC cycle, keeping the ordinary nonstagnation constant
independent of the requested spectral threshold.
Source: complete actual ordinary model conditioning, precise measured spectral
radius transfer and true active-gate full-history execution comparison.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- One nonstagnation and model constant chosen before every gate threshold gives exact ordinary/gated full-history equality on a true threshold-dependent source tube.
Use: Supply the genuine operator-class trajectory assertion in gated part (iii).
Article: main_krylov, thm:UCg(iii).
Proof: Choose the actual ordinary constants using a fixed auxiliary threshold one half. Shrink only the real perturbation radius for the requested spectral margin. The same original active ordinary models pass that threshold. Genuine defined gated curvatures then make each actual current direction nonzero, so induction through the real executor gives exact complete-history equality, including all measured queries and their observations.
-/
theorem gated_defined_uniform_nonstagnating_eq_rfc (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ C : ℝ, 0<M₀ ∧ 0<C ∧
      ∀ γ : ℝ, 0<γ → γ<1 → ∃ ε₀ : ℝ, 0<ε₀ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤ε₀ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      gatedFullRunDefined γ A B g n →
      (∀ k≤n, methodRun (gatedMethod fullMemory γ) A B g k=methodRun (rfcMethod fullMemory 1) A B g k) ∧
        activeObservedModelBounds base (rfcMethod fullMemory 1) A B g n γ C ε := by
  obtain ⟨M,δ,C,hM,hδ,hC,hmodels⟩ := ordinary_uniform_active_models n hn κ hκ
  refine ⟨M,C,hM,hC,?_⟩
  intro γ hγ hγ1
  obtain ⟨r,hr,hgate⟩ := uniform_model_gate_radius hC.le hγ hγ1
  refine ⟨min δ r,lt_min hδ hr,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB hdefined
  have hmodel := hmodels base hb μ hμ hspec A B g ε hε (he.trans (min_le_left _ _)) hinit hpre hN hA hB
  obtain ⟨hδ1,hmargin⟩ := hgate ε hε.le (he.trans (min_le_right _ _))
  have hnew := activeObservedModelBounds_threshold base hb _ A B g n hmodel (mul_nonneg hC.le hε.le) hδ1 hmargin
  refine ⟨?_,hnew⟩
  apply gated_defined_cycle_eq_rfc_of_active_gates γ A B g n hdefined
  intro i hi
  dsimp only
  intro hd
  exact (hnew i hi hd).2.1

end
end krylov.Correction
