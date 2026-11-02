import krylov.Information.RankBaseCurve
import krylov.Information.MetricComparison

/-!
Article: main_krylov, thm:C, own-base normalization of actual lower witnesses.
Use: choose the true positive metric and CG normalization tube once, before
all source budget profiles and both signed physical base perturbations.
Source: exact lower-base identification, proved true CG reference-error
variation, genuine full-atom preservation and actual dual metric comparison.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.LinearAlgebra krylov.Stability krylov.Correction
open scoped MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Both signed lower-scenario physical bases lie on the same actual rank-one reference curve.
Use: apply one proved normalization tube to every original profile and both signs.
Article: main_krylov, thm:C, actual lower-base identification.
Proof: the source hidden base has only its terminal rank-one diagonal;
its genuine physical transport is precisely the defined rank-one base curve. -/
theorem physical_planarLowerScenario_base (A : Matrix (Fin n) (Fin n) ℝ)
    (e f : EuclideanSpace ℝ (Fin n)) (ω : ℕ → ℝ) (w : ℝ) (N : ℕ) (a γ σ : ℝ) :
    let W := ∑ i∈range N, ω i
    ((planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹).base=
      rankBaseCurve A f (σ*(1-W)*γ*W) := by
  simp only [Scenario.inPhysical,Scenario.mapForms,planarLowerScenario,rankBaseCurve,
    planarMatrix,zero_smul,add_zero]

/-- One fixed true reference tube controls every actual signed lower base, its full active spectral count, own error normalization and dual residual metric.
Use: discharge every own-base normalization premise of the all-profile minimax lower bound.
Article: main_krylov, thm:C, uniform normalization of the actual admissible lower scenarios.
Proof: the exact scenario base is on the real rank-one curve, and its proved
physical budget bounds that curve parameter by W₀. The genuine reference
normalization tube supplies positivity, full activity and the relative φ bound.
The actual signed base domination and exact rank-one budget comparison control
every actual output gradient in its own inverse metric.
-/
theorem planarLowerScenario_normalization {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ ε L : ℝ, 0<ε ∧ 0<L ∧ ∀ (ω : ℕ → ℝ) (w a γ σ : ℝ),
      (∀ i∈range N, 0≤ω i) → 0≤w → (∑ i∈range N, ω i)<ε →
      0≤γ → a^2+γ^2=1 → σ^2=1 →
      let W := ∑ i∈range N, ω i
      let S := (planarLowerScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
        ω w N a γ σ).inPhysical (metricRoot A)⁻¹
      ∃ hB : S.base.PosDef, referenceAtomCount S.base hB g=N+1 ∧
        0<‖cgCanonicalError S.base g N‖ ∧
        ‖cgCanonicalError S.base g N‖≤‖cgCanonicalError A g N‖*(1+L*W) ∧
        ∀ v, ‖cgOperator (metricRoot A)⁻¹ v‖≤(1+W)*‖cgOperator (metricRoot S.base)⁻¹ v‖ := by
  -- Derive the one true reference tube before choosing any source budget profile.
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  have hf : ‖f‖=1 := by simpa only [f,Fin.val_last] using ho.norm_eq_one (Fin.last N)
  obtain ⟨ε,L,hε,hL,hcontrol⟩ := rankBaseCurve_reference_control A hA g hcount f hf
  refine ⟨min ε 1,L,lt_min hε (by norm_num),hL,?_⟩
  intro ω w a γ σ hω hw hW hγ hcircle hσ
  let W := ∑ i∈range N, ω i
  let S := (planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹
  let δ := σ*(1-W)*γ*W
  have hW₀ : 0≤W := sum_nonneg hω
  have hW₁ : W<1 := hW.trans_le (min_le_right _ _)
  have hS := cg_planarLowerScenario_admissible A hA g hN hcount ω w 0 W hω hw le_rfl hW₁ le_rfl a γ σ hγ hcircle hσ
  have hbase : S.base=rankBaseCurve A f δ := physical_planarLowerScenario_base A e f ω w N a γ σ
  have hδ : |δ|≤W := by
    have hn := hS.2.1
    rw [hbase,rankBaseCurve_budget A hA f hf] at hn
    exact hn
  obtain ⟨hB,hfull,hφ,hφupper⟩ := hcontrol δ (hδ.trans_lt (hW.trans_le (min_le_left _ _)))
  have hupper : S.base≤(1+W) • A :=
    (relative_displacement_base A S.base hA hS.1.1.isSymm hW₀ hW₁ hS.2.1).2.1
  have hφupper' : ‖cgCanonicalError S.base g N‖≤‖cgCanonicalError A g N‖*(1+L*W) := by
    rw [hbase]
    exact hφupper.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hδ hL.le)) (norm_nonneg _))
  change ∃ hB : S.base.PosDef, referenceAtomCount S.base hB g=N+1 ∧
    0<‖cgCanonicalError S.base g N‖ ∧
    ‖cgCanonicalError S.base g N‖≤‖cgCanonicalError A g N‖*(1+L*W) ∧
      ∀ v, ‖cgOperator (metricRoot A)⁻¹ v‖≤(1+W)*‖cgOperator (metricRoot S.base)⁻¹ v‖
  refine ⟨hS.1,?_,?_,hφupper',?_⟩
  · simpa only [hbase] using hfull
  · simpa only [hbase] using hφ
  · intro v
    exact dual_norm_le_of_base_upper A S.base hA hS.1 (by linarith : 1≤1+W) hupper v

end
end krylov.Information
