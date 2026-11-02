import krylov.Correction.UniformOrdinaryResponse
import krylov.Correction.ResponseHomogeneity
import krylov.Correction.GatedUniformBounds

/-!
Article: main_krylov, thm:UCq, original-scale whole-class cubic expansion.
Use: Cover every actual initial gradient and all nonnegative primitive source
budgets with the same dimension-and-condition-ratio constants and radius.
Source: the proved normalized genuine terminal theorem, exact RFC/CG
homogeneity, positive normalization invariance and scalar vanishing at zero.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The actual original-source uniform cubic expansion holds for arbitrary initial metric error and every sufficiently small positive source budget.
Use: Restore the precise initial-error factor in the genuine whole spectral-class estimate.
Article: main_krylov, thm:UCq.
Proof: Normalize the actual positive initial metric error. Exact CG homogeneity preserves the full active atom count and scales (N); exact real RFC homogeneity preserves the last-direction condition and returned gradient. Positive normalization leaves the true old flags, staircase and fresh defect unchanged. Cancel only the common positive initial scale.
-/
theorem ordinary_uniform_source_response_positive (k : ℕ) (hk : 0<k) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ω₀ C : ℝ, 0<M₀ ∧ 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ),
      0<ω → ω≤ω₀ → referenceAtomCount base hb g=k+1 →
      M₀*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
      m.direction (methodRun m A B g k)≠0 →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (k+1))+
        ‖cgCanonicalError base g k‖ • staircaseOperator base g
          (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
          (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤C*ω^3*‖cgCanonicalError base g 0‖ := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_source_response_unit k hk κ hκ
  refine ⟨M,δ,C,hM,hδ,hC,?_⟩
  intro base hb μ hμ hspec Θ g ω hω he hcount hN hE hF
  dsimp only
  intro hdir
  let A := scenarioProbe base Θ.val
  let B := scenarioCorrection base Θ.val
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  let J := cgOperator (metricRoot base)⁻¹
  let E := matrixSequenceExtension k Θ.val.1
  let F := matrixSequenceExtension (k+1) Θ.val.2 k
  let r := ‖cgCanonicalError base g 0‖
  let c := r⁻¹
  let g₁ := c • g
  have hg : g≠0 := cg_nonstagnation base hb g 0 (by omega)
  have hr : 0<r := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg)
  have hc : 0<c := inv_pos.mpr hr
  have hinit : ‖cgCanonicalError base g₁ 0‖=1 := by
    dsimp only [g₁]
    rw [cgCanonicalError_scalar base hb g c hc.ne' 0,norm_smul,Real.norm_of_nonneg hc.le]
    exact inv_mul_cancel₀ hr.ne'
  have hcount₁ : referenceAtomCount base hb g₁=k+1 :=
    (referenceAtomCount_scalar base hb g c hc.ne').trans hcount
  have hN₁ : M*ω≤‖cgCanonicalError base g₁ (k+1-2)‖ := by
    dsimp only [g₁]
    rw [cgCanonicalError_scalar base hb g c hc.ne' (k+1-2),norm_smul,Real.norm_of_nonneg hc.le]
    have ht := (le_div_iff₀ hr).mpr hN
    simpa only [div_eq_mul_inv,mul_comm] using ht
  have hdir₁ : m.direction (methodRun m A B g₁ k)≠0 := by
    rw [((rfc_scalar fullMemory 1 A B g c hc.ne' (k+1)).2 k (by omega)).1]
    exact smul_ne_zero hc.ne' hdir
  have ht := hbound base hb μ hμ hspec Θ g₁ ω hω he hinit hcount₁ hN₁ hE hF hdir₁
  have hvector : J (probedGradient m A B g₁ (k+1))+
      ‖cgCanonicalError base g₁ k‖ • staircaseOperator base g₁ E F (k+1) (freshDefect base g₁ E (k+1))=
      c • (J (probedGradient m A B g (k+1))+
        ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1))) := by
    dsimp only [g₁]
    rw [(rfc_scalar fullMemory 1 A B g c hc.ne' (k+1)).1,map_smul,
      cgCanonicalError_scalar base hb g c hc.ne' k,norm_smul,Real.norm_of_nonneg hc.le,
      staircaseOperator_positive_scalar base hb g hc,freshDefect_positive_scalar base hb g hc,
      smul_add,smul_smul]
  change ‖J (probedGradient m A B g₁ (k+1))+
    ‖cgCanonicalError base g₁ k‖ • staircaseOperator base g₁ E F (k+1) (freshDefect base g₁ E (k+1))‖≤C*ω^3 at ht
  rw [hvector,norm_smul,Real.norm_of_nonneg hc.le] at ht
  have hdiv : ‖J (probedGradient m A B g (k+1))+
      ‖cgCanonicalError base g k‖ • staircaseOperator base g E F (k+1) (freshDefect base g E (k+1))‖/r≤C*ω^3 := by
    simpa only [div_eq_inv_mul] using ht
  exact (div_le_iff₀ hr).mp hdiv

/-- The actual ordinary-RFC cubic expansion is uniform on the complete original spectral class under (N), including arbitrary initial scales and zero source budgets.
Use: Apply the original terminal formula with one radius and constant chosen before every reference, spectral scale and finite symmetric scenario.
Article: main_krylov, thm:UCq.
Proof: Positive budgets use the proved original-scale expansion. At zero budget, the same unchanged actual scenario satisfies every positive allowance. Its genuine preterminal CG error supplies a positive allowance satisfying (N). The common cubic bound, restricted to a unit radius, gives a common quadratic bound at arbitrarily small allowances, which forces the actual remainder norm to vanish.
-/
theorem ordinary_uniform_source_response (k : ℕ) (hk : 0<k) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ω₀ C : ℝ, 0<M₀ ∧ 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ),
      0≤ω → ω≤ω₀ → referenceAtomCount base hb g=k+1 →
      M₀*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
      m.direction (methodRun m A B g k)≠0 →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (k+1))+
        ‖cgCanonicalError base g k‖ • staircaseOperator base g
          (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
          (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤C*ω^3*‖cgCanonicalError base g 0‖ := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_source_response_positive k hk κ hκ
  refine ⟨M,δ,C,hM,hδ,hC,?_⟩
  intro base hb μ hμ hspec Θ g ω hω he hcount hN hE hF
  by_cases hpos : 0<ω
  · exact hbound base hb μ hμ hspec Θ g ω hpos he hcount hN hE hF
  · have hz : ω=0 := le_antisymm (by linarith) hω
    subst ω
    dsimp only
    intro hdir
    let A := scenarioProbe base Θ.val
    let B := scenarioCorrection base Θ.val
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
    let r := ‖cgCanonicalError base g 0‖
    let q := ‖cgCanonicalError base g (k+1-2)‖
    let x := ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (k+1))+
      ‖cgCanonicalError base g k‖ • staircaseOperator base g
        (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
        (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖
    have hg : g≠0 := cg_nonstagnation base hb g 0 (by omega)
    have hr : 0<r := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg)
    have hq : 0<q := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb
      (CG.gradient (cgOperator base) g (k+1-2)) (cg_nonstagnation base hb g (k+1-2) (by omega)))
    let t₀ := min δ (min 1 (q/(M*r)))
    have ht₀ : 0<t₀ := lt_min hδ (lt_min zero_lt_one (div_pos hq (mul_pos hM hr)))
    have hzero : x=0 := nonnegative_quadratic_vanish (norm_nonneg _) (mul_nonneg hC.le hr.le) ht₀ (by
      intro t ht htd
      have htδ : t≤δ := htd.le.trans (min_le_left _ _)
      have ht1 : t≤1 := htd.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hprod : t*(M*r)≤q := (le_div_iff₀ (mul_pos hM hr)).mp
        (htd.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
      have hNt : M*t*r≤q := by nlinarith only [hprod]
      have htbound := hbound base hb μ hμ hspec Θ g t ht htδ hcount hNt
        (fun i => (hE i).trans ht.le) (fun i => (hF i).trans ht.le) hdir
      change x≤C*t^3*r at htbound
      have hcube : t^3≤t^2 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
      calc
        x ≤ C*t^3*r := htbound
        _ = (C*r)*t^3 := by ring
        _ ≤ (C*r)*t^2 := mul_le_mul_of_nonneg_left hcube (mul_nonneg hC.le hr.le))
    change x≤C*(0 : ℝ)^3*r
    simp only [hzero,zero_pow (by decide : (3 : ℕ)≠0),mul_zero,zero_mul,le_refl]

end
end krylov.Correction
