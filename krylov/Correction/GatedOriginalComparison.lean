import krylov.Correction.GatedUniformComparison
import krylov.Correction.SpectralHistoryScaling
import krylov.Correction.GatedHomogeneousDomains
import krylov.Stability.UniformFCScaling
import krylov.Reference.EnergyMinimum

/-!
Article: main_krylov, thm:UCg(iii), complete original-scale actual gate comparison.
Use: Remove initial-gradient normalization and include zero operator budgets
in the exact ordinary/gated full-history and measured-test conclusions.
Source: proved real uniform normalized models, genuine complete-history and
spectral-decision homogeneity, and actual active reference error positivity.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- One nonstagnation constant before every gate threshold yields exact original-scale full-history equality and every actual passed spectral test on a genuine positive-budget source tube.
Use: Apply gated part (iii) on original actual initial data and all boundary budgets.
Article: main_krylov, thm:UCg(iii).
Proof: The actual defined run gives a positive initial metric norm. Normalize it using the proved true domain and CG error covariance, apply the genuine uniform comparison, and restore complete histories and all actual spectral decisions by their exact nonzero-scale identities.
-/
theorem gated_uniform_nonstagnating_history (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ : ℝ, 0<M₀ ∧
      ∀ γ : ℝ, 0<γ → γ<1 → ∃ ε₀ : ℝ, 0<ε₀ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤ε₀ →
      (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      gatedFullRunDefined γ A B g n →
      (∀ k≤n, methodRun (gatedMethod fullMemory γ) A B g k=methodRun (rfcMethod fullMemory 1) A B g k) ∧
        actualSpectralGates (gatedMethod fullMemory γ) fullMemory A B g n γ := by
  obtain ⟨M,_C,hM,_hC,hbound⟩ := gated_defined_uniform_nonstagnating_eq_rfc n hn κ hκ
  refine ⟨M,hM,?_⟩
  intro γ hγ hγ1
  obtain ⟨δ,hδ,hmodel⟩ := hbound γ hγ hγ1
  refine ⟨δ,hδ,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hpre hN hA hB hdefined
  let r := ‖cgCanonicalError base g 0‖
  let g₁ := r⁻¹ • g
  have hr : 0<r := gated_defined_initial_metric_pos base hb γ A B g n (by omega) hdefined
  have hc : r⁻¹≠0 := inv_ne_zero hr.ne'
  have hdefined₁ := gatedFullRunDefined_scalar γ A B g r⁻¹ hc n hdefined
  have hinit₁ : ‖cgCanonicalError base g₁ 0‖≤1 := by
    dsimp only [g₁]
    rw [cgCanonicalError_scalar base hb g r⁻¹ hc 0,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    change r⁻¹*r≤1
    rw [inv_mul_cancel₀ hr.ne']
  have hpre₁ i (hi : i<n) : CG.gradient (cgOperator base) g₁ i≠0 := by
    dsimp only [g₁]
    rw [cg_gradient_scalar base hb g r⁻¹ hc i]
    exact smul_ne_zero hc (hpre i hi)
  have hN₁ : M*ε≤‖cgCanonicalError base g₁ (n-2)‖ := by
    dsimp only [g₁]
    rw [cgCanonicalError_scalar base hb g r⁻¹ hc (n-2),norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    have hd : M*ε≤‖cgCanonicalError base g (n-2)‖/r := (le_div_iff₀ hr).mpr hN
    simpa only [div_eq_mul_inv,mul_comm] using hd
  have hnormalized := hmodel base hb μ hμ hspec A B g₁ ε hε he hinit₁ hpre₁ hN₁ hA hB hdefined₁
  have heq := hnormalized.1
  have hg : r • g₁=g := by dsimp only [g₁]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  refine ⟨?_,?_⟩
  · intro k hk
    have hsG := gated_complete_history_scalar fullMemory γ A B g₁ r hr.ne' k
    have hsR := rfc_complete_history_scalar fullMemory 1 A B g₁ r hr.ne' k
    rw [hg] at hsG hsR
    exact hsG.trans ((congrArg (scaleHistory r) (heq k hk)).trans hsR.symm)
  · have hgate₁ : actualSpectralGates (gatedMethod fullMemory γ) fullMemory A B g₁ n γ := by
      dsimp only [actualSpectralGates]
      intro i hi
      have hd : (gatedMethod fullMemory γ).direction (methodRun (gatedMethod fullMemory γ) A B g₁ i)≠0 := by
        intro hz
        have hc := (hdefined₁ i hi).2
        rw [hz,map_zero,inner_zero_left] at hc
        exact hc rfl
      have heqi := heq i hi.le
      have hdr : (rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g₁ i)≠0 := by
        rw [heqi] at hd
        exact hd
      have ht := (hnormalized.2 i hi hdr).2.1
      rw [← heqi] at ht
      exact ht
    have hscale := gated_actualSpectralGates_scalar fullMemory γ A B g₁ r hr.ne' n
    rw [hg] at hscale
    exact hscale.mpr hgate₁


/-- The original-scale actual nonstagnating ordinary/gated history and all measured gate conclusions hold also at zero perturbation budget with the same constant and radius.
Use: Apply gated part (iii) on original actual initial data and all boundary budgets.
Article: main_krylov, thm:UCg(iii).
Proof: Positive budgets use the genuine original-scale theorem. At zero budget the fixed actual operators obey every positive allowance. Full actual CG activity gives a positive penultimate reference error, so one explicit smaller positive allowance satisfies both the original nonstagnation condition and the common radius. Apply the same real theorem to the unchanged actual run.
-/
theorem gated_uniform_nonstagnating_history_nonnegative (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ : ℝ, 0<M₀ ∧
      ∀ γ : ℝ, 0<γ → γ<1 → ∃ ε₀ : ℝ, 0<ε₀ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0≤ε → ε≤ε₀ →
      (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      gatedFullRunDefined γ A B g n →
      (∀ k≤n, methodRun (gatedMethod fullMemory γ) A B g k=methodRun (rfcMethod fullMemory 1) A B g k) ∧
        actualSpectralGates (gatedMethod fullMemory γ) fullMemory A B g n γ := by
  obtain ⟨M,hM,hbound⟩ := gated_uniform_nonstagnating_history n hn κ hκ
  refine ⟨M,hM,?_⟩
  intro γ hγ hγ1
  obtain ⟨δ,hδ,hpositive⟩ := hbound γ hγ hγ1
  refine ⟨δ,hδ,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hpre hN hA hB hdefined
  by_cases hpos : 0<ε
  · exact hpositive base hb μ hμ hspec A B g ε hpos he hpre hN hA hB hdefined
  · have hz : ε=0 := le_antisymm (by linarith) hε
    subst ε
    let r := ‖cgCanonicalError base g 0‖
    let q := ‖cgCanonicalError base g (n-2)‖
    have hr : 0<r := gated_defined_initial_metric_pos base hb γ A B g n (by omega) hdefined
    have hq : 0<q := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb
      (CG.gradient (cgOperator base) g (n-2)) (hpre (n-2) (by omega)))
    let t := min (δ/2) (q/(2*M*r))
    have ht : 0<t := lt_min (half_pos hδ) (div_pos hq (by positivity))
    have htd : t≤δ := (min_le_left _ _).trans (by linarith)
    have hprod : t*(2*M*r)≤q := (le_div_iff₀ (by positivity : 0<2*M*r)).mp (min_le_right _ _)
    have hNt : M*t*r≤q := by
      have hnonneg : 0≤M*t*r := by positivity
      nlinarith only [hprod,hnonneg]
    exact hpositive base hb μ hμ hspec A B g t ht htd hpre hNt
      (fun i hi => (hA i hi).trans ht.le) (fun i hi => (hB i hi).trans ht.le) hdefined

end
end krylov.Correction
