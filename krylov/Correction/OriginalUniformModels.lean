import krylov.Correction.UniformModelScaling
import krylov.Stability.UniformFCScaling
import krylov.Reference.EnergyMinimum

/-!
Article: main_krylov, thm:UCq, original-scale ordinary observed models.
Use: Complete the uniform actual inverse, gate and step-normalized model
statement for arbitrary initial data, every positive spectral scale and zero budgets.
Source: the proved normalized nonstagnating induction and exact actual model
scale covariance; active CG errors are genuinely positive before exhaustion.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- Ordinary RFC has uniform genuine active inverse, gate and normalized-model bounds on the full positive-budget spectral class with arbitrary physical initial gradients.
Use: Restore the original scale in the actual ordinary model and gate part of the uniform theorem.
Article: main_krylov, thm:UCq.
Proof: Full CG activity gives a positive actual initial metric error. Normalize it by its reciprocal, apply the proved true nonstagnating observed-model theorem, and restore the exact original models, inverses and measured tests using genuine positive-scale covariance.
-/
theorem ordinary_uniform_original_active_models_positive (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ε₀ C : ℝ, 0<M₀ ∧ 0<ε₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤ε₀ →
      (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      activeObservedModelBounds base (rfcMethod fullMemory 1) A B g n (1/2) C ε := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_active_models n hn κ hκ
  refine ⟨M,δ,C,hM,hδ,hC,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hpre hN hA hB
  let r := ‖cgCanonicalError base g 0‖
  let g₁ := r⁻¹ • g
  have hg : g≠0 := hpre 0 (by omega)
  have hr : 0<r := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg)
  have hc : r⁻¹≠0 := inv_ne_zero hr.ne'
  have hinit₁ : ‖cgCanonicalError base g₁ 0‖≤1 := by
    dsimp only [g₁]
    rw [cgCanonicalError_scalar base hb g r⁻¹ hc 0,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    change r⁻¹*r≤1
    rw [inv_mul_cancel₀ hr.ne']
  have hpre₁ i (hi : i<n) : CG.gradient (cgOperator base) g₁ i≠0 := by
    dsimp only [g₁]
    rw [cg_gradient_scalar base hb g r⁻¹ hc i]
    exact smul_ne_zero hc (hpre i hi)
  have hN₁ : M*ε≤‖cgCanonicalError base g₁ (n-2)‖ := by
    dsimp only [g₁]
    rw [cgCanonicalError_scalar base hb g r⁻¹ hc (n-2),norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    have ht := (le_div_iff₀ hr).mpr hN
    simpa only [div_eq_mul_inv,mul_comm] using ht
  have hnormalized := hbound base hb μ hμ hspec A B g₁ ε hε he hinit₁ hpre₁ hN₁ hA hB
  have hrestored := ordinary_active_models_scalar base A B g₁ hr n (1/2) C ε hnormalized
  have hrestore : r • g₁=g := by dsimp only [g₁]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rwa [hrestore] at hrestored

/-- One common dimension-and-condition-ratio tube controls every genuine active ordinary-RFC inverse, both measured gates and its original step-normalized model, including zero budgets and arbitrary initial scales.
Use: Complete the original operator-class model and gate conclusions under condition (N).
Article: main_krylov, thm:UCq.
Proof: Positive budgets use the actual original-scale theorem. At zero budget the unchanged true operators satisfy every smaller positive allowance. Actual preterminal CG errors provide a positive allowance satisfying (N), giving all real inverse and gate conclusions. Applying the same bound on arbitrarily smaller allowances forces the actual normalized model error to be exactly zero.
-/
theorem ordinary_uniform_original_active_models (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ε₀ C : ℝ, 0<M₀ ∧ 0<ε₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0≤ε → ε≤ε₀ →
      (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      activeObservedModelBounds base (rfcMethod fullMemory 1) A B g n (1/2) C ε := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_original_active_models_positive n hn κ hκ
  refine ⟨M,δ,C,hM,hδ,hC,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hpre hN hA hB
  by_cases hpos : 0<ε
  · exact hbound base hb μ hμ hspec A B g ε hpos he hpre hN hA hB
  · have hz : ε=0 := le_antisymm (by linarith) hε
    subst ε
    let r := ‖cgCanonicalError base g 0‖
    let q := ‖cgCanonicalError base g (n-2)‖
    have hg : g≠0 := hpre 0 (by omega)
    have hr : 0<r := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg)
    have hq : 0<q := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb
      (CG.gradient (cgOperator base) g (n-2)) (hpre (n-2) (by omega)))
    let t₀ := min (δ/2) (q/(2*M*r))
    have ht₀ : 0<t₀ := lt_min (half_pos hδ) (div_pos hq (by positivity))
    have htδ : t₀≤δ := (min_le_left _ _).trans (by linarith)
    have hprod : t₀*(2*M*r)≤q := (le_div_iff₀ (by positivity : 0<2*M*r)).mp (min_le_right _ _)
    have hNt : M*t₀*r≤q := by nlinarith [show 0≤M*t₀*r by positivity]
    have hall t (ht : 0<t) (hle : t≤t₀) :
        activeObservedModelBounds base (rfcMethod fullMemory 1) A B g n (1/2) C t := by
      apply hbound base hb μ hμ hspec A B g t ht (hle.trans htδ) hpre
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hM.le) hr.le).trans hNt)
      · intro i hi
        exact (hA i hi).trans ht.le
      · intro i hi
        exact (hB i hi).trans ht.le
    have hfirst := hall t₀ ht₀ le_rfl
    dsimp only [activeObservedModelBounds] at hfirst ⊢
    intro k hk hd
    have ht := hfirst k hk hd
    refine ⟨ht.1,ht.2.1,ht.2.2.1,?_⟩
    rw [mul_zero]
    by_contra hnot
    let x := ‖canonicalObservedModel base
      (((rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g k),
        A k ((rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g k)))::
          selectedWindow fullMemory (methodRun (rfcMethod fullMemory 1) A B g k))-1‖
    have hx : 0<x := lt_of_not_ge hnot
    let t := min t₀ (x/(2*C))
    have htpos : 0<t := lt_min ht₀ (div_pos hx (by positivity))
    have hsmall : t≤t₀ := min_le_left _ _
    have hxt : t*(2*C)≤x := (le_div_iff₀ (by positivity : 0<2*C)).mp (min_le_right _ _)
    have hxbound : x≤C*t := (hall t htpos hsmall k hk hd).2.2.2
    nlinarith

end
end krylov.Correction
