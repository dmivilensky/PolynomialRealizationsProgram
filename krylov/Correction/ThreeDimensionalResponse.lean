import krylov.Correction.UniformPrefixResponse
import krylov.Correction.ThreeDimensionalPrefix
import krylov.Correction.ResponseHomogeneity
import krylov.Correction.GatedUniformBounds

/-!
Article: main_krylov, thm:UCq, original three-dimensional uniform exception.
Use: Apply the genuine full-source cubic terminal expansion without (N),
at every positive spectral scale, initial-gradient scale and nonnegative budget.
Source: the derived exceptional actual prefix, shared measured terminal
assembly, exact real RFC/CG homogeneity and zero-budget scalar vanishing.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- In dimension three the original-source ordinary-RFC cubic expansion is uniform for unit initial metric error without (N) or a lower intermediate CG energy.
Use: Discharge the three-dimensional exception using the same actual terminal reconstruction as the nonstagnating theorem.
Article: main_krylov, thm:UCq.
Proof: The proved exceptional three-step tube derives every actual prefix bound with no nonstagnation premise. Instantiate the shared true terminal assembly with the unrestricted condition; all original source geometry and executor identities are unchanged.
-/
theorem ordinary_three_dimensional_source_response_unit (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (2+1)) (Fin (2+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (Θ : symmetricScenarios (2+1) (2+1)) (g : EuclideanSpace ℝ (Fin (2+1))) (ω : ℝ),
      0<ω → ω≤ω₀ → ‖cgCanonicalError base g 0‖=1 → referenceAtomCount base hb g=2+1 →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (2+1)))
      m.direction (methodRun m A B g 2)≠0 →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (2+1))+
        ‖cgCanonicalError base g 2‖ • staircaseOperator base g
          (matrixSequenceExtension 2 Θ.val.1) (matrixSequenceExtension (2+1) Θ.val.2 2) (2+1)
          (freshDefect base g (matrixSequenceExtension 2 Θ.val.1) (2+1))‖≤C*ω^3 := by
  obtain ⟨δ,a,Cr,D,Cξ,Cm,hδ,ha,hCr,hD,hCξ,hCm,hprefix⟩ := ordinary_three_step_terminal_prefix (n := 3)
  obtain ⟨ρ,C,hρ,hC,hbound⟩ := ordinary_uniform_source_response_unit_of_prefix 2 (by omega) κ hκ
    (fun _ _ _ => True) hδ ha hCr hD hCξ (by
      intro base hb μ hμ hspec A B g ε hA0 hε he hinit hpre _ hA hB
      exact hprefix base hb A B g ε hA0 hε he hinit (fun i hi => hpre i (by omega)) hA hB)
  refine ⟨ρ,C,hρ,hC,?_⟩
  intro base hb μ hμ hspec Θ g ω hω he hinit hcount hE hF
  exact hbound base hb μ hμ hspec Θ g ω hω he hinit hcount True.intro hE hF

/-- The genuine three-dimensional original uniform cubic formula has its precise arbitrary initial-error factor for every small positive source budget, with no condition (N).
Use: Restore the physical initial scale in the exceptional source theorem.
Article: main_krylov, thm:UCq.
Proof: Normalize the true positive initial metric error. Exact real RFC and CG homogeneity restore the terminal gradient and penultimate-error scale, while actual normalized CG directions, old flags, staircase and fresh defect stay fixed.
-/
theorem ordinary_three_dimensional_source_response_positive (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (2+1)) (Fin (2+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (Θ : symmetricScenarios (2+1) (2+1)) (g : EuclideanSpace ℝ (Fin (2+1))) (ω : ℝ),
      0<ω → ω≤ω₀ → referenceAtomCount base hb g=2+1 →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (2+1)))
      m.direction (methodRun m A B g 2)≠0 →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (2+1))+
        ‖cgCanonicalError base g 2‖ • staircaseOperator base g
          (matrixSequenceExtension 2 Θ.val.1) (matrixSequenceExtension (2+1) Θ.val.2 2) (2+1)
          (freshDefect base g (matrixSequenceExtension 2 Θ.val.1) (2+1))‖≤C*ω^3*‖cgCanonicalError base g 0‖ := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := ordinary_three_dimensional_source_response_unit κ hκ
  refine ⟨δ,C,hδ,hC,?_⟩
  intro base hb μ hμ hspec Θ g ω hω he hcount hE hF
  dsimp only
  intro hdir
  let A := scenarioProbe base Θ.val
  let B := scenarioCorrection base Θ.val
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (2+1)))
  let J := cgOperator (metricRoot base)⁻¹
  let E := matrixSequenceExtension 2 Θ.val.1
  let F := matrixSequenceExtension (2+1) Θ.val.2 2
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
  have hcount₁ : referenceAtomCount base hb g₁=2+1 :=
    (referenceAtomCount_scalar base hb g c hc.ne').trans hcount
  have hdir₁ : m.direction (methodRun m A B g₁ 2)≠0 := by
    rw [((rfc_scalar fullMemory 1 A B g c hc.ne' (2+1)).2 2 (by omega)).1]
    exact smul_ne_zero hc.ne' hdir
  have ht := hbound base hb μ hμ hspec Θ g₁ ω hω he hinit hcount₁ hE hF hdir₁
  have hvector : J (probedGradient m A B g₁ (2+1))+
      ‖cgCanonicalError base g₁ 2‖ • staircaseOperator base g₁ E F (2+1) (freshDefect base g₁ E (2+1))=
      c • (J (probedGradient m A B g (2+1))+
        ‖cgCanonicalError base g 2‖ • staircaseOperator base g E F (2+1) (freshDefect base g E (2+1))) := by
    dsimp only [g₁]
    rw [(rfc_scalar fullMemory 1 A B g c hc.ne' (2+1)).1,map_smul,
      cgCanonicalError_scalar base hb g c hc.ne' 2,norm_smul,Real.norm_of_nonneg hc.le,
      staircaseOperator_positive_scalar base hb g hc,freshDefect_positive_scalar base hb g hc,
      smul_add,smul_smul]
  change ‖J (probedGradient m A B g₁ (2+1))+
    ‖cgCanonicalError base g₁ 2‖ • staircaseOperator base g₁ E F (2+1) (freshDefect base g₁ E (2+1))‖≤C*ω^3 at ht
  rw [hvector,norm_smul,Real.norm_of_nonneg hc.le] at ht
  have hdiv : ‖J (probedGradient m A B g (2+1))+
      ‖cgCanonicalError base g 2‖ • staircaseOperator base g E F (2+1) (freshDefect base g E (2+1))‖/r≤C*ω^3 := by
    simpa only [div_eq_inv_mul] using ht
  exact (div_le_iff₀ hr).mp hdiv

/-- The complete original three-dimensional uniform cubic expansion holds without (N), including arbitrary initial scales, all positive spectral scales and zero budgets.
Use: Apply the printed exceptional terminal formula to every original finite symmetric scenario in one common tube.
Article: main_krylov, thm:UCq.
Proof: Positive budgets use the proved actual scale-restored exceptional theorem. A zero-budget scenario satisfies the same actual expansion bound at every sufficiently small positive allowance; scalar vanishing forces its true remainder norm to be zero.
-/
theorem ordinary_three_dimensional_source_response (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (2+1)) (Fin (2+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (Θ : symmetricScenarios (2+1) (2+1)) (g : EuclideanSpace ℝ (Fin (2+1))) (ω : ℝ),
      0≤ω → ω≤ω₀ → referenceAtomCount base hb g=2+1 →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (2+1)))
      m.direction (methodRun m A B g 2)≠0 →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (2+1))+
        ‖cgCanonicalError base g 2‖ • staircaseOperator base g
          (matrixSequenceExtension 2 Θ.val.1) (matrixSequenceExtension (2+1) Θ.val.2 2) (2+1)
          (freshDefect base g (matrixSequenceExtension 2 Θ.val.1) (2+1))‖≤C*ω^3*‖cgCanonicalError base g 0‖ := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := ordinary_three_dimensional_source_response_positive κ hκ
  refine ⟨δ,C,hδ,hC,?_⟩
  intro base hb μ hμ hspec Θ g ω hω he hcount hE hF
  by_cases hpos : 0<ω
  · exact hbound base hb μ hμ hspec Θ g ω hpos he hcount hE hF
  · have hz : ω=0 := le_antisymm (by linarith) hω
    subst ω
    dsimp only
    intro hdir
    let A := scenarioProbe base Θ.val
    let B := scenarioCorrection base Θ.val
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (2+1)))
    let r := ‖cgCanonicalError base g 0‖
    let x := ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (2+1))+
      ‖cgCanonicalError base g 2‖ • staircaseOperator base g
        (matrixSequenceExtension 2 Θ.val.1) (matrixSequenceExtension (2+1) Θ.val.2 2) (2+1)
        (freshDefect base g (matrixSequenceExtension 2 Θ.val.1) (2+1))‖
    have hg : g≠0 := cg_nonstagnation base hb g 0 (by omega)
    have hr : 0<r := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg)
    let t₀ := min δ 1
    have ht₀ : 0<t₀ := lt_min hδ zero_lt_one
    have hzero : x=0 := nonnegative_quadratic_vanish (norm_nonneg _) (mul_nonneg hC.le hr.le) ht₀ (by
      intro t ht htd
      have htδ : t≤δ := htd.le.trans (min_le_left _ _)
      have ht1 : t≤1 := htd.le.trans (min_le_right _ _)
      have htbound := hbound base hb μ hμ hspec Θ g t ht htδ hcount
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
