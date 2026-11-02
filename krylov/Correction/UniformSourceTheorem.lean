import krylov.Correction.OriginalUniformResponse
import krylov.Correction.ScenarioUniformModels

/-!
Article: main_krylov, thm:UCq, complete original ordinary uniform conclusion under (N).
Use: Apply the actual inverse, both measured gates, normalized-model estimate,
cubic expansion and sharp all-profile upper bound with one common triple of
dimension-and-condition-ratio constants.
Source: the proved original-scale source model and cubic theorems and the
sharp compression inequality on the genuine CG flags and fresh defect.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The complete ordinary uniform conclusion on one actual original finite source scenario.
Use: Share the identical real model, gate, cubic and all-profile sharp statements between the nonstagnating and low-dimensional cases.
Article: main_krylov, thm:UCq.
-/
def ordinarySourceUniformConclusion {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (Θ : symmetricScenarios (k+1) (k+1))
    (g : EuclideanSpace ℝ (Fin (k+1))) (C ω : ℝ) : Prop :=
  let A := scenarioProbe base Θ.val
  let B := scenarioCorrection base Θ.val
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  activeObservedModelBounds base m A B g (k+1) (1/2) C ω ∧
  (m.direction (methodRun m A B g k)≠0 →
    ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (k+1))+
      ‖cgCanonicalError base g k‖ • staircaseOperator base g
        (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
        (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤C*ω^3*‖cgCanonicalError base g 0‖ ∧
    ∀ (w : ℕ → ℝ) (w' : ℝ),
      (∀ i∈range k, ‖matrixSequenceExtension k Θ.val.1 i‖≤w i) →
      ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤w' →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (k+1))‖≤
        ‖cgCanonicalError base g k‖*sharpConstant (∑ i∈range k, w i) w'+C*ω^3*‖cgCanonicalError base g 0‖)

/-- Any proved remainder estimate for the actual original-source terminal expansion gives the sharp original budget-profile bound on the same returned gradient.
Use: Preserve the exact source constant K while sharing the genuine cubic tube.
Article: main_krylov, thm:UCq.
Proof: Apply the existing sharp compression theorem to the actual symmetric source increments and real CG flags. Keep the genuine penultimate error norm on that leading vector and use the norm triangle inequality for the actual returned gradient.
-/
theorem ordinary_source_sharp_upper {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1)))
    (hcount : referenceAtomCount base hb g=k+1) {r : ℝ}
    (hrem : ‖cgOperator (metricRoot base)⁻¹
      (probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (k+1))+
      ‖cgCanonicalError base g k‖ • staircaseOperator base g
        (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
        (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤r)
    (w : ℕ → ℝ) (w' : ℝ)
    (hw : ∀ i∈range k, ‖matrixSequenceExtension k Θ.val.1 i‖≤w i)
    (hw' : ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤w') :
    ‖cgOperator (metricRoot base)⁻¹
      (probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (k+1))‖≤
      ‖cgCanonicalError base g k‖*sharpConstant (∑ i∈range k, w i) w'+r := by
  have hbound := reference_second_order_bound base hb g hcount.ge (by omega : 0<k+1)
    (matrixSequenceExtension k Θ.val.1) (fun i _ => symmetricScenario_increment_symm Θ i)
    (matrixSequenceExtension (k+1) Θ.val.2 k) w hw hw'
  simp only [Nat.add_sub_cancel] at hbound
  let v := staircaseOperator base g (matrixSequenceExtension k Θ.val.1)
    (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1) (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))
  have hv : ‖‖cgCanonicalError base g k‖ • v‖≤‖cgCanonicalError base g k‖*sharpConstant (∑ i∈range k, w i) w' := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  have ht := norm_sub_le
    (cgOperator (metricRoot base)⁻¹
      (probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (k+1))+
      ‖cgCanonicalError base g k‖ • v) (‖cgCanonicalError base g k‖ • v)
  rw [add_sub_cancel_right] at ht
  exact ht.trans ((add_le_add hrem hv).trans_eq (add_comm _ _))

set_option maxHeartbeats 600000 in
/-- One common triple controls the genuine ordinary-RFC models, inverse and measured decisions together with both original whole spectral-class terminal inequalities under (N), at every initial and positive spectral scale and including zero budgets.
Use: This is the complete ordinary uniform source theorem under its original nonstagnation hypothesis, with every individual sharp budget profile quantified after the common constants.
Article: main_krylov, thm:UCq.
Proof: Add the genuine original-source nonstagnation constants, intersect their positive radii and enlarge their allowances to one positive constant. The original spectral interval yields the actual condition-ratio interval. Apply the proved actual model and cubic results on that same scenario; the exact CG sharp compression bound gives the second printed inequality for every original budget profile.
-/
theorem ordinary_uniform_source_theorem (k : ℕ) (hk : 0<k) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ω₀ C : ℝ, 0<M₀ ∧ 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ),
      0≤ω → ω≤ω₀ → referenceAtomCount base hb g=k+1 →
      M₀*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      ordinarySourceUniformConclusion base Θ g C ω := by
  obtain ⟨Mm,δm,Cm,hMm,hδm,hCm,hmodels⟩ := ordinary_uniform_scenario_models (k+1) (by omega) κ hκ
  obtain ⟨Mr,δr,Cr,hMr,hδr,hCr,hresponse⟩ := ordinary_uniform_source_response k hk κ hκ
  refine ⟨Mm+Mr,min δm δr,Cm+Cr,by positivity,lt_min hδm hδr,by positivity,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hcount hN hE hF
  have hspec' i : μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ := by
    have hL := (div_le_iff₀ hμ).mp hratio
    exact ⟨(hspec i).1,by nlinarith [(hspec i).2]⟩
  have hNm : Mm*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : Mm≤Mm+Mr) hω) (norm_nonneg _)).trans hN
  have hNr : Mr*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖ :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : Mr≤Mm+Mr) hω) (norm_nonneg _)).trans hN
  have hm := hmodels base hb μ L hμ hratio hspec Θ.val g ω hω (he.trans (min_le_left _ _)) hcount hNm hE hF
  dsimp only [ordinarySourceUniformConclusion]
  refine ⟨?_,?_⟩
  · dsimp only [activeObservedModelBounds] at hm ⊢
    intro j hj hd
    have ht := hm j hj hd
    refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith : Cm≤Cm+Cr) hω
  · intro hd
    have hr := hresponse base hb μ hμ hspec' Θ g ω hω (he.trans (min_le_right _ _)) hcount hNr hE hF hd
    have ht := hr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Cr≤Cm+Cr) (pow_nonneg hω 3)) (norm_nonneg _))
    refine ⟨ht,?_⟩
    intro w w' hw hw'
    exact ordinary_source_sharp_upper base hb Θ g hcount ht w w' hw hw'

end
end krylov.Correction
