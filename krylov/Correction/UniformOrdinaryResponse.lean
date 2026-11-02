import krylov.Correction.UniformPrefixResponse

/-!
Article: main_krylov, thm:UCq, whole spectral-class ordinary cubic response.
Use: Choose one nonstagnation constant, radius and cubic allowance before every
positive reference, spectral scale and original finite symmetric scenario.
Source: the genuine nonstagnating prefix, measured terminal reconstruction,
weighted true CG flags and exact original source/executor coordinate identities.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

set_option maxHeartbeats 1600000 in
/-- The genuine ordinary-RFC terminal expansion has a common cubic remainder on the full original spectral class under (N), with unit initial metric error and no last-step lower bound.
Use: Establish the normalized original-source uniform expansion before restoring arbitrary initial scales and zero budgets.
Article: main_krylov, thm:UCq.
Proof: Fix the real prefix constants before every reference. A smaller numerical tube derives both inverse margins and the full measured Gram and model estimates from actual secants. The genuine observed-search theorem bounds the last line without inverting its CG energy. True recorded-step errors give the reference-weighted flag estimate. Apply the exact original-source terminal-response theorem and convert the dimension-scaled operator allowance back to the primitive source budget.
-/
theorem ordinary_uniform_source_response_unit (k : ℕ) (hk : 0<k) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ω₀ C : ℝ, 0<M₀ ∧ 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ),
      0<ω → ω≤ω₀ → ‖cgCanonicalError base g 0‖=1 → referenceAtomCount base hb g=k+1 →
      M₀*ω≤‖cgCanonicalError base g (k+1-2)‖ →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
      m.direction (methodRun m A B g k)≠0 →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (k+1))+
        ‖cgCanonicalError base g k‖ • staircaseOperator base g
          (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
          (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤C*ω^3 := by
  obtain ⟨M,δ,a,Cr,D,Cξ,Cm,hM,hδ,ha,hCr,hD,hCξ,hCm,hprefix⟩ :=
    ordinary_uniform_terminal_prefix (k+1) (by omega) κ hκ
  let condition := fun (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (ε : ℝ) => M*ε≤‖cgCanonicalError base g (k+1-2)‖
  have hprovider : ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
        (g : EuclideanSpace ℝ (Fin (k+1))) (ε : ℝ), A 0=cgOperator base → 0<ε → ε≤δ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<k+1, CG.gradient (cgOperator base) g i≠0) →
      condition base g ε →
      (∀ i<k+1, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1)))‖≤ε) →
      (∀ i<k+1, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1)))‖≤ε) →
      ordinaryTerminalPrefixBounds base A B g a Cr D Cξ Cm ε := by
    intro base hb μ hμ hspec A B g ε _ hε he hinit hpre hN hA hB
    exact hprefix base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  obtain ⟨ρ,C,hρ,hC,hbound⟩ := ordinary_uniform_source_response_unit_of_prefix k hk κ hκ condition hδ ha hCr hD hCξ hprovider
  let Jn : ℝ := ((k+1 : ℕ) : ℝ)+1
  have hJn : 0<Jn := by dsimp only [Jn]; positivity
  refine ⟨M*Jn,ρ,C,mul_pos hM hJn,hρ,hC,?_⟩
  intro base hb μ hμ hspec Θ g ω hω he hinit hcount hN hE hF
  apply hbound base hb μ hμ hspec Θ g ω hω he hinit hcount ?_ hE hF
  dsimp only [condition]
  dsimp only [Jn] at hN
  nlinarith only [hN]

end
end krylov.Correction
