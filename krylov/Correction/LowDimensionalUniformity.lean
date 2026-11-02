import krylov.Correction.ThreeDimensionalModels
import krylov.Correction.ThreeDimensionalResponse
import krylov.Correction.UniformSourceTheorem

/-!
Article: Theorem B.25 [thm:UCq] of krylov.tex.
Use: Apply the same actual model, gate, cubic and sharp budget-profile
conclusions under (N), or without (N) in dimensions two and three.
Source: the completed genuine whole spectral-class theorem, the exceptional
actual second recorded-pair induction and exact source/scale restoration.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The complete original two-dimensional ordinary uniform theorem needs no nonstagnation condition, at every initial and spectral scale and including zero budgets.
Use: Cover the first printed low-dimensional exception with all actual models, gates and both terminal inequalities.
Article: main_krylov, thm:UCq.
Proof: In dimension two the penultimate reference error is exactly the initial error. The common radius at most the reciprocal nonstagnation constant makes (N) automatic on the same original scenario.
-/
theorem ordinary_two_dimensional_uniformity (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : symmetricScenarios 2 2) (g : EuclideanSpace ℝ (Fin 2)) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=2 →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      ordinarySourceUniformConclusion base Θ g C ω := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_source_theorem 1 (by omega) κ hκ
  refine ⟨min δ (1/M),C,lt_min hδ (by positivity),hC,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hcount hE hF
  have hMω : M*ω≤1 := by
    have ht := (le_div_iff₀ hM).mp (he.trans (min_le_right _ _))
    nlinarith only [ht]
  have hN : M*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (1+1-2)‖ := by
    simpa only [show (1+1-2 : ℕ)=0 by omega,one_mul] using mul_le_mul_of_nonneg_right hMω (norm_nonneg (cgCanonicalError base g 0))
  exact hbound base hb μ L hμ hratio hspec Θ g ω hω (he.trans (min_le_left _ _)) hcount hN hE hF

/-- The complete original three-dimensional ordinary uniform theorem needs no condition (N), including all actual model and gate conclusions and both cubic and sharp terminal inequalities at arbitrary scales and zero budgets.
Use: Close the genuine three-dimensional exception even near vanishing intermediate CG energy.
Article: main_krylov, thm:UCq.
Proof: Intersect the independently derived actual exceptional model and cubic source tubes and add their constants. Both arise from the genuine second recorded-pair induction with no minimum-energy premise. The original exact CG compression bound supplies every sharp budget-profile inequality on that same returned gradient.
-/
theorem ordinary_three_dimensional_uniformity (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin 3) (Fin 3) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : symmetricScenarios 3 3) (g : EuclideanSpace ℝ (Fin 3)) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=3 →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      ordinarySourceUniformConclusion base Θ g C ω := by
  obtain ⟨δm,Cm,hδm,hCm,hmodels⟩ := ordinary_three_dimensional_scenario_models κ hκ
  obtain ⟨δr,Cr,hδr,hCr,hresponse⟩ := ordinary_three_dimensional_source_response κ hκ
  refine ⟨min δm δr,Cm+Cr,lt_min hδm hδr,by positivity,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hcount hE hF
  have hspec' i : μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ := by
    have hL := (div_le_iff₀ hμ).mp hratio
    exact ⟨(hspec i).1,by nlinarith [(hspec i).2]⟩
  have hm := hmodels base hb μ L hμ hratio hspec Θ.val g ω hω (he.trans (min_le_left _ _)) hcount hE hF
  dsimp only [ordinarySourceUniformConclusion]
  refine ⟨?_,?_⟩
  · dsimp only [activeObservedModelBounds] at hm ⊢
    intro j hj hd
    have ht := hm j hj hd
    refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith : Cm≤Cm+Cr) hω
  · intro hd
    have hr := hresponse base hb μ hμ hspec' Θ g ω hω (he.trans (min_le_right _ _)) hcount hE hF hd
    have ht := hr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Cr≤Cm+Cr) (pow_nonneg hω 3)) (norm_nonneg _))
    refine ⟨ht,?_⟩
    intro w w' hw hw'
    exact ordinary_source_sharp_upper base hb Θ g hcount ht w w' hw hw'

/-- Both source low-dimensional exceptions share the complete original uniform conclusion without (N).
Use: Apply the printed n≤3 clause with every genuine boundary and scale case retained.
Article: main_krylov, thm:UCq.
Proof: The original positive cycle length and dimension bound leave exactly the proved two- and three-dimensional cases.
-/
theorem ordinary_low_dimensional_uniformity (k : ℕ) (hk : 0<k) (hlow : k≤2) (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=k+1 →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      ordinarySourceUniformConclusion base Θ g C ω := by
  have hcases : k=1 ∨ k=2 := by omega
  rcases hcases with rfl | rfl
  · exact ordinary_two_dimensional_uniformity κ hκ
  · exact ordinary_three_dimensional_uniformity κ hκ

/-- The full original ordinary-RFC uniform theorem, with constants depending only on dimension and condition ratio, every positive spectral scale, arbitrary initial gradient, all nonnegative source budgets and the unconditional n≤3 exceptions.
Use: This is the completed ordinary part of the source uniform spectral-gate theorem, including real inverse/model/gate conclusions and both printed terminal estimates.
Article: main_krylov, thm:UCq.
Proof: Choose the actual low-dimensional tube before all data when n≤3. Otherwise use the completed original nonstagnating tube and its genuine hypothesis (N). Every conclusion refers to the actual original finite-source executor and its true reference CG geometry.
-/
theorem ordinary_uniformity (k : ℕ) (hk : 0<k) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ω₀ C : ℝ, 0<M₀ ∧ 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=k+1 →
      (k+1≤3 ∨ M₀*ω*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (k+1-2)‖) →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      ordinarySourceUniformConclusion base Θ g C ω := by
  by_cases hlow : k≤2
  · obtain ⟨δ,C,hδ,hC,hbound⟩ := ordinary_low_dimensional_uniformity k hk hlow κ hκ
    refine ⟨1,δ,C,zero_lt_one,hδ,hC,?_⟩
    intro base hb μ L hμ hratio hspec Θ g ω hω he hcount _ hE hF
    exact hbound base hb μ L hμ hratio hspec Θ g ω hω he hcount hE hF
  · obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_source_theorem k hk κ hκ
    refine ⟨M,δ,C,hM,hδ,hC,?_⟩
    intro base hb μ L hμ hratio hspec Θ g ω hω he hcount hcondition hE hF
    have hN := hcondition.resolve_left (by omega)
    exact hbound base hb μ L hμ hratio hspec Θ g ω hω he hcount hN hE hF

end
end krylov.Correction
