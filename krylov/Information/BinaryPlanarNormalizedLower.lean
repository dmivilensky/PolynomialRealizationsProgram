import krylov.Information.BinaryPlanarDictionary
import krylov.Information.BinaryPlanarLower
import krylov.Information.NormalizedLower

/-!
Article: main_krylov, thm:H, the gradient-only planar lower bound in the
original scenario's own metric and its own true CG error normalization.
Use: the indistinguishable compatible tensors are actual members of the
same full binary source class used by the upper estimate. All constants
precede the source scale and every competing policy.
Source: the proved binary information radius and genuine rank-one base
regularity; no prescribed response or normalization is assumed.
-/
namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods krylov.Stability
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- A genuine physical compatible binary lower witness, including its hidden base.
Article: main_krylov, thm:H, the two actual signed source scenarios. -/
def binaryPlanarWitnessScenario (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (κ r σ : ℝ) : Scenario (N+1) :=
  let t := gradientWitness r σ
  (binaryPlanarScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
    κ r (-κ*(t.t2+r*t.t3)) N t).inPhysical (metricRoot A)⁻¹

/-- The physical base in every compatible binary scenario is the genuine rank-one reference curve.
Article: main_krylov, thm:H, true unknown-base normalization. -/
theorem physical_binaryPlanarScenario_base (A : Matrix (Fin n) (Fin n) ℝ)
    (e h : EuclideanSpace ℝ (Fin n)) (κ r β : ℝ) (N : ℕ) (t : BinaryCubic) :
    ((binaryPlanarScenario e h κ r β N t).inPhysical (metricRoot A)⁻¹).base =
      rankBaseCurve A h β := by
  simp only [Scenario.inPhysical, Scenario.mapForms, binaryPlanarScenario,
    rankBaseCurve, planarMatrix, zero_smul, zero_add]

/-- One actual reference tube controls both binary lower witnesses uniformly in all source scales.
Article: main_krylov, thm:H, own-base metric and genuine last-error comparison. -/
theorem binaryPlanarWitness_normalization
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1)))
    (hcount : referenceAtomCount A hA g=N+1) (r : ℝ) (hr : 0≤r) :
    ∃ ε L : ℝ, 0<ε ∧ 0<L ∧ ∀ κ e_c σ : ℝ,
      0≤κ → κ≤e_c → e_c<ε → σ^2=1 →
      let S := binaryPlanarWitnessScenario A g κ r σ
      ∃ hB : S.base.PosDef, referenceAtomCount S.base hB g=N+1 ∧
        0<‖cgCanonicalError S.base g N‖ ∧
        ‖cgCanonicalError S.base g N‖≤‖cgCanonicalError A g N‖*(1+L*e_c) ∧
        ∀ v, ‖cgOperator (metricRoot A)⁻¹ v‖≤(1+e_c)*‖cgOperator (metricRoot S.base)⁻¹ v‖ := by
  let h := canonicalCGUnitStep A g N
  have hh : ‖h‖=1 := (canonicalCG_frame_of_full_atoms A hA g hcount).norm_eq_one (Fin.last N)
  obtain ⟨ε,L,hε,hL,hcontrol⟩ := rankBaseCurve_reference_control A hA g hcount h hh
  refine ⟨min ε 1,L,lt_min hε (by norm_num),hL,?_⟩
  intro κ e_c σ hκ hκe hec hσ
  let S := binaryPlanarWitnessScenario A g κ r σ
  let β := -κ*((gradientWitness r σ).t2+r*(gradientWitness r σ).t3)
  have hbase : S.base=rankBaseCurve A h β := physical_binaryPlanarScenario_base A _ h κ r β N _
  have hβ : |β|≤e_c := by
    dsimp only [β]
    rw [gradientWitness_hidden r σ κ]
    exact gradientWitness_base_bound hr hσ hκ hκe
  obtain ⟨hB,hfull,hφ,hup⟩ := hcontrol β (hβ.trans_lt (hec.trans_le (min_le_left _ _)))
  have hB' : S.base.PosDef := by simpa only [hbase] using hB
  have hbudget : relativeBudget A (S.base-A)≤e_c := by
    rw [hbase,rankBaseCurve_budget A hA h hh]
    exact hβ
  have hec₀ := hκ.trans hκe
  have hupper := (relative_displacement_base A S.base hA hB'.1.isSymm hec₀
    (hec.trans_le (min_le_right _ _)) hbudget).2.1
  change ∃ hB : S.base.PosDef, referenceAtomCount S.base hB g=N+1 ∧
    0<‖cgCanonicalError S.base g N‖ ∧
    ‖cgCanonicalError S.base g N‖≤‖cgCanonicalError A g N‖*(1+L*e_c) ∧
    ∀ v, ‖cgOperator (metricRoot A)⁻¹ v‖≤(1+e_c)*‖cgOperator (metricRoot S.base)⁻¹ v‖
  refine ⟨hB',by simpa only [hbase] using! hfull,by simpa only [hbase] using hφ,?_,?_⟩
  · rw [hbase]
    exact hup.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hβ hL.le)) (norm_nonneg _))
  · exact fun v => dual_norm_le_of_base_upper A S.base hA hB' (by linarith) hupper v

/-- A controlled own-base normalization preserves a quadratic coefficient with a relative linear loss.
Article: main_krylov, thm:H, uniform normalization of the planar radius. -/
theorem normalized_radius_relative_loss {K R D C B s : ℝ}
    (hK : 0≤K) (hR : 0≤R) (hC : 0≤C) (hB : 0≤B) (hs : 0≤s)
    (hD : D≤1+B*s) (hlower : K*(1-C*s)≤D*R) :
    K*(1-(C+B)*s)≤R := by
  by_cases hKR : K≤R
  · exact (mul_le_of_le_one_right hK (by linarith [mul_nonneg (add_nonneg hC hB) hs] : 1-(C+B)*s≤1)).trans hKR
  · have hRK : R≤K := le_of_not_ge hKR
    have hupper := mul_le_mul_of_nonneg_right hD hR
    have hprod := mul_le_mul_of_nonneg_left hRK (mul_nonneg hB hs)
    nlinarith

/-- The original gradient-only binary source lower bound holds for every true method in the precise own-base output ratio.
Article: main_krylov, thm:H, the printed planar coefficient 1/[2(1+r)²].
The two output ratios are executions of actual compatible full source
scenarios, with true positive full-atom bases and their true last CG errors. -/
theorem binaryPlanar_normalized_lower
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) (r : ℝ) (hr : 0≤r) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧ ∀ κ e_c : ℝ,
      0≤κ → κ≤e_c → e_c<ε →
      ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))), CGConsistent m → OneCorrectionMethod m →
      (κ^2/(2*(1+r)^2))*(1-C*e_c) ≤
        max ((binaryPlanarWitnessScenario A g κ r 1).outputRatio m g N)
          ((binaryPlanarWitnessScenario A g κ r (-1)).outputRatio m g N) := by
  obtain ⟨ε₁,C,hε₁,hC,hlower⟩ := binaryPlanar_gradient_lower A hA g hN hcount r hr
  obtain ⟨ε₂,L,hε₂,hL,hnorm⟩ := binaryPlanarWitness_normalization A hA g hcount r hr
  refine ⟨min ε₁ (min ε₂ 1),C+(1+2*L),lt_min hε₁ (lt_min hε₂ (by norm_num)),by positivity,?_⟩
  intro κ e_c hκ hκe hec m hm h1
  have hec₀ := hκ.trans hκe
  have hec₁ : e_c≤1 := (hec.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  let S := fun σ => binaryPlanarWitnessScenario A g κ r σ
  let a := ‖cgCanonicalError A g N‖
  let D := (1+e_c)*(1+L*e_c)
  let R := max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N)
  obtain ⟨hBp,_,hφp,hup,hmp⟩ := hnorm κ e_c 1 hκ hκe
    (hec.trans_le ((min_le_right _ _).trans (min_le_left _ _))) (by norm_num)
  obtain ⟨hBm,_,hφm,hum,hmm⟩ := hnorm κ e_c (-1) hκ hκe
    (hec.trans_le ((min_le_right _ _).trans (min_le_left _ _))) (by norm_num)
  have hp := Scenario.outputRatio_reference_bound (S 1) m g N A a (1+e_c) (1+L*e_c)
    (by positivity) hφp hmp hup
  have hm' := Scenario.outputRatio_reference_bound (S (-1)) m g N A a (1+e_c) (1+L*e_c)
    (by positivity) hφm hmm hum
  have hcoef : 0≤a*D := by dsimp only [a,D]; positivity
  have hmax : max
      ‖cgOperator (metricRoot A)⁻¹ (probedGradient m (S 1).probeOracle ((S 1).correctionOracle N) g (N+1))‖
      ‖cgOperator (metricRoot A)⁻¹ (probedGradient m (S (-1)).probeOracle ((S (-1)).correctionOracle N) g (N+1))‖≤a*D*R :=
    max_le (hp.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hcoef))
      (hm'.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hcoef))
  have href := (hlower κ e_c hκ hκe (hec.trans_le (min_le_left _ _)) m hm h1).2.2.2
  dsimp only at href
  rw [← binaryPlanarScenario_gradient_cancelled A hA g hN hcount m hm,
    ← binaryPlanarScenario_gradient_cancelled A hA g hN hcount m hm] at href
  have henergy : sqrt (cgEnergy A g N)=a :=
    (cgEnergy_sqrt A hA g N).trans (terminal_step_error_norm A hA g (by omega)).symm
  rw [henergy] at href
  have ha : 0<a := canonical_error_pos A hA _ (cg_nonstagnation A hA g N (by omega))
  have hnormalized : (κ^2/(2*(1+r)^2))*(1-C*e_c)≤D*R :=
    (mul_le_mul_iff_left₀ ha).mp (by simpa only [mul_assoc,mul_comm,mul_left_comm,S,binaryPlanarWitnessScenario] using href.trans hmax)
  have hR : 0≤R := le_trans (div_nonneg (norm_nonneg _) hφp.le) (le_max_left _ _)
  have hD : D≤1+(1+2*L)*e_c := by
    have hsq : e_c^2≤e_c := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq hL.le
    dsimp only [D]
    nlinarith
  exact normalized_radius_relative_loss (by positivity) hR hC.le (by positivity) hec₀ hD hnormalized

end
end krylov.Information
