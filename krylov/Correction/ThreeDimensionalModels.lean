import krylov.Correction.ThreeDimensionalPrefix
import krylov.Correction.ScenarioUniformModels

/-!
Article: main_krylov, thm:UCq, original three-dimensional exceptional models.
Use: Cover every original actual active model, inverse and both measured tests
without (N), at all initial and positive spectral scales and zero budgets.
Source: the true exceptional ordinary prefix, exact actual normalized-model
homogeneity and the completed zero-budget nonstagnating source theorem.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

set_option maxHeartbeats 800000 in
/-- All true three-dimensional ordinary-RFC models, inverse domains and both measured decisions obey a common original-source linear tube without condition (N), including arbitrary initial scales and zero budgets.
Use: Supply the complete model and gate portion of the printed low-dimensional exception.
Article: main_krylov, thm:UCq.
Proof: Normalize the genuine nonzero initial metric error and apply the derived actual three-step prefix at four times the primitive source budget. Exact positive model covariance restores the same original measured matrices and inverse domains. At zero budget, (N) is automatic and the existing original-source model theorem gives precisely zero normalized model error.
-/
theorem ordinary_three_dimensional_scenario_models (κ : ℝ) (hκ : 1≤κ) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin 3) (Fin 3) ℝ) (hb : base.PosDef) (μ L : ℝ), 0<μ → L/μ≤κ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤L) →
      ∀ (Θ : CanonicalScenario 3 3) (g : EuclideanSpace ℝ (Fin 3)) (ω : ℝ), 0≤ω → ω≤ω₀ →
      referenceAtomCount base hb g=3 →
      (∀ i, ‖Θ.1 i‖≤ω) → (∀ i, ‖Θ.2 i‖≤ω) →
      activeObservedModelBounds base (rfcMethod fullMemory 1)
        (scenarioProbe base Θ) (scenarioCorrection base Θ) g 3 (1/2) C ω := by
  obtain ⟨δp,a,Cr,D,Cξ,Cp,hδp,ha,hCr,hD,hCξ,hCp,hprefix⟩ := ordinary_three_step_terminal_prefix (n := 3)
  obtain ⟨Mz,δz,Cz,hMz,hδz,hCz,hzero⟩ := ordinary_uniform_scenario_models 3 (by omega) κ hκ
  refine ⟨min (δp/4) δz,4*Cp+Cz,lt_min (by positivity) hδz,by positivity,?_⟩
  intro base hb μ L hμ hratio hspec Θ g ω hω he hcount hE hF
  let A := scenarioProbe base Θ
  let B := scenarioCorrection base Θ
  have hm : activeObservedModelBounds base (rfcMethod fullMemory 1) A B g 3 (1/2) (4*Cp+Cz) ω := by
    by_cases hpos : 0<ω
    · let r := ‖cgCanonicalError base g 0‖
      let g₁ := r⁻¹ • g
      have hg : g≠0 := cg_nonstagnation base hb g 0 (by omega)
      have hr : 0<r := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg)
      have hc : r⁻¹≠0 := inv_ne_zero hr.ne'
      have hinit : ‖cgCanonicalError base g₁ 0‖≤1 := by
        dsimp only [g₁]
        rw [cgCanonicalError_scalar base hb g r⁻¹ hc 0,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        change r⁻¹*r≤1
        rw [inv_mul_cancel₀ hr.ne']
      have hpre i (hi : i≤1) : CG.gradient (cgOperator base) g₁ i≠0 := by
        dsimp only [g₁]
        rw [cg_gradient_scalar base hb g r⁻¹ hc i]
        exact smul_ne_zero hc (cg_nonstagnation base hb g i (by omega))
      have hA0 : A 0=cgOperator base := by
        simp only [A,scenarioProbe,canonicalFCPath,cumulativeDrift,range_zero,sum_empty,
          Matrix.mul_zero,Matrix.zero_mul,map_zero,one_smul,add_zero]
      have heδ : 4*ω≤δp := by
        have ht := (le_div_iff₀ (by norm_num : (0 : ℝ)<4)).mp (he.trans (min_le_left _ _))
        nlinarith only [ht]
      have hp := hprefix base hb A B g₁ (4*ω) hA0 (by positivity) heδ hinit hpre
        (fun i hi => by simpa only [Nat.cast_ofNat,show (3 : ℝ)+1=4 by norm_num] using (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).1)
        (fun i hi => by simpa only [Nat.cast_ofNat,show (3 : ℝ)+1=4 by norm_num] using (scenario_canonical_operator_budgets base hb Θ hω hE hF i hi).2)
      have ht := ordinary_active_models_scalar base A B g₁ hr 3 (1/2) Cp (4*ω) hp.1
      have hrestore : r • g₁=g := by dsimp only [g₁]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
      rw [hrestore] at ht
      dsimp only [activeObservedModelBounds] at ht ⊢
      intro j hj hd
      have hx := ht j hj hd
      refine ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.trans ?_⟩
      nlinarith [mul_nonneg hCz.le hω]
    · have hz : ω=0 := le_antisymm (by linarith) hω
      subst ω
      have hN : Mz*0*‖cgCanonicalError base g 0‖≤‖cgCanonicalError base g (3-2)‖ := by
        simp only [mul_zero,zero_mul]; exact norm_nonneg _
      have ht := hzero base hb μ L hμ hratio hspec Θ g 0 (le_refl _) (by positivity) hcount hN hE hF
      dsimp only [activeObservedModelBounds] at ht ⊢
      intro j hj hd
      have hx := ht j hj hd
      refine ⟨hx.1,hx.2.1,hx.2.2.1,?_⟩
      simpa only [mul_zero] using hx.2.2.2
  exact hm

end
end krylov.Correction
